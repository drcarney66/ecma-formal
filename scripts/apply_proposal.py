#!/usr/bin/env python3
"""Apply a TC39 proposal's specification text to ECMA-262's spec.html.

    scripts/apply_proposal.py BASE PROPOSAL OUT [--resolutions FILE] [--report FILE.json] [--force]
                              [--check SPEC-GEN]

BASE is a spec.html; PROPOSAL is a proposal's `spec.emu` or the directory that holds it (its `img/` beside it);
OUT is the spec.html written; beside it go the files it imports (from beside BASE) and the proposal's figures
(`img/`). `scripts/spec_text.py` calls this for each proposal `spec/proposals.txt` names; run by hand, it is for
trying a proposal out.

A proposal's spec.emu is written as a diff against ECMA-262: it reproduces the clauses it changes, marking
what it adds `<ins>` and what it removes `<del>`, and adds clauses of its own. This tool reads that diff and
applies it. It works clause by clause, matching a clause by its `id`:

- A clause whose id the base has is merged block by block. Its own content (what is not a child clause) is cut
  into top-level blocks (`h1`, `p`, `dl`, `emu-alg`, `emu-grammar`, `emu-table`, `emu-note`, …). A block's *old
  text* is the block with its `<ins>` dropped and its `<del>` kept; its *new text* is the reverse. The old text
  must equal a base block of the same clause, after the previous matched block, white space aside; that base
  block becomes the new text. Failing that, the old text is compared loosely: without the punctuation a dropped
  `<ins>` leaves behind (`f(_x_, )`, `{ a, }`, ` .`), rows whose cells all went, and the case of a step's first
  letter.
  - A block with no markup is context: it must be in the base, and nothing changes.
  - A block that is all `<ins>` is inserted after the previous matched block, but only when the proposal shows
    every base block up to that point; otherwise where it goes is a question (`place`).
  - A definition grammar (`<emu-grammar type="definition">`) is merged rule by rule, by left-hand side.
  - A table that differs from the base as a whole is merged row by row: every old row must be a base row.
  - A block whose new text already equals the base is reported as "already upstream" and left alone.
  - The proposal's own attributes on the clause are kept where the base lacks them (`oldids`); `number=` is
    the proposal's numbering and is ignored. An editor's note (`<emu-note type="editor">`) is dropped.
- A clause whose id the base does not have is new: it is inserted, its markup resolved, after the base clause
  of its previous sibling in the proposal, or else before its next sibling, or else last in its parent.
- A clause whose `h1` is wholly `<del>` is removed, once its old text is found to be the base's; a clause with
  id `del-X` removes the base's clause `X`.
- Everything the proposal does not show is kept byte for byte.

It refuses, naming the clause and the block and showing the differing lines, wherever the old text is not the
base's: a refusal is a question the merge cannot answer from the text alone. Nothing is written while one is
unanswered (`--force` writes anyway, for inspection). A resolutions file answers them, one per line (`#`
comments; a reason may follow on the line):

    ignore CLAUSE BLOCK            the block is context the proposal abbreviated (an omitted `<dt>`): skip it
    place CLAUSE BLOCK after N     an inserted block goes after the clause's base block N (the proposal
                                   omitted the base blocks around it)
    rebase CLAUSE BLOCK            the base is newer than the text the proposal was written against: apply the
                                   proposal's change (old -> new) to the base block by a three-way merge of
                                   lines; on an unmarked line where the base and the proposal's old text
                                   differ, the base's line stays; a conflict is a refusal
    rebase-take CLAUSE BLOCK       the same, but the proposal's line wins there: the proposal changed the text
                                   without marking it
    use-new CLAUSE BLOCK           the proposal's new text replaces the base block, whatever the base says
    keep-base CLAUSE BLOCK         the base block stays; the proposal's change to it is dropped
    patch CLAUSE BLOCK "OLD" ==> "NEW"   the base block stays, with this substitution (the proposal's change
                                   restated on the newer text; OLD, a JSON string, occurs exactly once)
    rename OLD NEW                 a name the proposal renames: every whole-word use in the result is renamed,
                                   in the clauses the proposal does not show too

CLAUSE is a clause id; BLOCK is a position among the proposal clause's own blocks, counting from 0, as the
refusal shows it; N is a position among the base clause's own blocks.

After the merge it checks, and prints, that every `<ins>` text is in the result and no `<del>` text is (unless
the proposal re-inserts it), and that the result's clause tree is the base's less the removed clauses and plus
the inserted ones. It warns (not a refusal) about a name the proposal removes or renames that the result still
uses where the proposal did not show it (an abstract operation's name, a link to a removed clause's id), which
a `rename` answers. With `--check SPEC-GEN`, it then runs that generator's parser round trip on the result
(`spec-gen --spec=OUT roundtrip`): every algorithm still parses and prints back as written."""

import argparse
import difflib
import json
import re
import sys

TAG_RE = re.compile(r"<(/?)(emu-clause|emu-annex)\b([^>]*)>")


class Node:
    def __init__(self, tag, attrs, open_start, open_end, parent):
        self.tag, self.attrs = tag, attrs
        self.open_start, self.open_end = open_start, open_end
        self.close_start = self.close_end = None
        self.children = []
        self.parent = parent
        m = re.search(r'\bid="([^"]*)"', attrs)
        self.id = m.group(1) if m else None

    def own_segments(self):
        segs, pos = [], self.open_end
        for c in self.children:
            segs.append((pos, c.open_start))
            pos = c.close_end
        segs.append((pos, self.close_start))
        return segs

    def walk(self):
        yield self
        for c in self.children:
            yield from c.walk()


def parse_tree(text):
    root = Node("root", "", 0, 0, None)
    root.close_start = root.close_end = len(text)
    cur = root
    for m in TAG_RE.finditer(text):
        close, tag, attrs = m.groups()
        if close:
            if cur.tag != tag:
                raise SystemExit(f"unbalanced </{tag}> at offset {m.start()}")
            cur.close_start, cur.close_end = m.start(), m.end()
            cur = cur.parent
        else:
            n = Node(tag, attrs, m.start(), m.end(), cur)
            cur.children.append(n)
            cur = n
    if cur is not root:
        raise SystemExit("unclosed clause")
    return root


def blocks(text, start, end):
    """Top-level blocks of text[start:end]: (s, e, kind) with kind a tag name, '#comment' or '#text'."""
    out, i = [], start
    while i < end:
        while i < end and text[i].isspace():
            i += 1
        if i >= end:
            break
        if text.startswith("<!--", i):
            j = text.index("-->", i) + 3
            out.append((i, j, "#comment"))
            i = j
            continue
        m = re.match(r"<([a-zA-Z][\w-]*)\b[^>]*?(/?)>", text[i:end])
        if not m:
            j = text.find("<", i + 1, end)
            j = end if j < 0 else j
            out.append((i, j, "#text"))
            i = j
            continue
        name = m.group(1)
        if m.group(2) or name in ("br", "img", "hr", "meta", "link"):
            out.append((i, i + m.end(), name))
            i += m.end()
            continue
        depth, k = 0, i
        pat = re.compile(r"<(/?)" + re.escape(name) + r"\b[^>]*>")
        for t in pat.finditer(text, i, end):
            depth += -1 if t.group(1) else 1
            if depth == 0:
                k = t.end()
                break
        else:
            raise SystemExit(f"unclosed <{name}> at offset {i}")
        out.append((i, k, name))
        i = k
    return out


INS = re.compile(r"<ins\b[^>]*>(.*?)</ins>", re.S)
DEL = re.compile(r"<del\b[^>]*>(.*?)</del>", re.S)


def resolve(s, keep):
    """keep='new': <ins> kept (tags dropped), <del> dropped with content; keep='old': the reverse.
    A line made empty by the removal, or left as a bare step marker, is removed."""
    out_lines = []
    for line in split_keep_markup_lines(s):
        if keep == "new":
            r = DEL.sub("", line)
            r = INS.sub(lambda m: m.group(1), r)
        else:
            r = INS.sub("", line)
            r = DEL.sub(lambda m: m.group(1), r)
        if r != line and (r.strip() == "" or re.fullmatch(r"\s*1\.\s*", r) or re.fullmatch(r"\s*\d+\.\s*", r)):
            # the whole line was markup: drop it (and a line the markup spans keeps its other lines)
            continue
        out_lines.append(r)
    res = "".join(out_lines)
    # a table row whose every cell the removal emptied goes too
    res = re.sub(r"[ \t]*<tr\b[^>]*>\s*(?:<t[dh]\b[^>]*>\s*</t[dh]>\s*)+</tr>[ \t]*\n?", "", res)
    return res


def split_keep_markup_lines(s):
    """Lines (with their newlines), but an <ins>/<del> that spans lines is kept in one piece with its lines."""
    lines = s.splitlines(keepends=True)
    out, buf = [], ""
    for l in lines:
        buf += l
        opens = len(re.findall(r"<(?:ins|del)\b", buf))
        closes = len(re.findall(r"</(?:ins|del)>", buf))
        if opens == closes:
            out.append(buf)
            buf = ""
    if buf:
        out.append(buf)
    return out


def norm(s):
    s = re.sub(r"<!--.*?-->", "", s, flags=re.S)
    s = re.sub(r"\s+", " ", s)
    s = re.sub(r"\s*(<[^>]+>)\s*", r"\1", s)
    return s.strip()


def loose(s):
    """norm, less the punctuation a removed <ins> leaves behind (`x, }`, `(x, )`, `x,  and`, ` .`), rows of empty
    cells, and the case of a step's first letter (`<ins>If …, … Else,</ins> let`)."""
    s = norm(s)
    s = re.sub(r"<tr\b[^>]*>(?:<td\b[^>]*></td>)+</tr>", "", s)
    s = re.sub(r"\s*([,.;:(){}\[\]])\s*", r"\1", s)
    s = re.sub(r",+([)}\]])", r"\1", s)
    s = re.sub(r",(and|or)\b", r" \1", s)
    s = re.sub(r",+", ",", s)
    s = re.sub(r"(^|\d\.|>)\s*([A-Za-z])", lambda m: m.group(1) + m.group(2).lower(), s)
    return s.strip()


def emptyish(s):
    """A block with no content left: only tags, white space and bare step markers."""
    t = re.sub(r"<[^>]+>", "", s)
    t = re.sub(r"(?m)^\s*1\.\s*$", "", t)
    return t.strip() == ""


def has_markup(s):
    return bool(re.search(r"<(?:ins|del)\b", s))


def line_indent(text, pos):
    ls = text.rfind("\n", 0, pos) + 1
    j = ls
    while j < len(text) and text[j] == " ":
        j += 1
    return j - ls


def reindent(block, delta):
    if delta == 0:
        return block
    lines = block.split("\n")
    out = [lines[0]]
    for l in lines[1:]:
        if not l.strip():
            out.append("")
        elif delta > 0:
            out.append(" " * delta + l)
        else:
            k = len(l) - len(l.lstrip(" "))
            out.append(l[min(k, -delta):])
    return "\n".join(out)


GRAM_LHS = re.compile(r"^(\s*)([A-Za-z_][\w]*)(\[[^\]]*\])?\s*(:{1,3})(.*)$")


def grammar_rules(body):
    """Rules of a definition grammar body: list of (lhs, text) split at blank lines."""
    rules, cur = [], []
    for l in body.split("\n"):
        if not l.strip():
            if cur:
                rules.append(cur)
                cur = []
            continue
        cur.append(l)
    if cur:
        rules.append(cur)
    out = []
    for r in rules:
        m = GRAM_LHS.match(r[0])
        out.append((m.group(2) if m else None, "\n".join(r)))
    return out


class Merger:
    def __init__(self, base, prop, resolutions):
        self.base, self.prop = base, prop
        self.btree, self.ptree = parse_tree(base), parse_tree(prop)
        self.bid = {n.id: n for n in self.btree.walk() if n.id}
        self.edits = []  # (start, end, text, why)
        self.refusals = []
        self.log = {"replaced": [], "inserted": [], "removed": [], "already": [], "context_ok": 0,
                    "blocks_replaced": [], "blocks_inserted": [], "blocks_removed": [], "grammar_rules": [],
                    "resolved": [], "renamed": [], "moved_or_reordered": [], "ignored_comments": 0,
                    "editor_notes_dropped": [], "attrs": [], "renamed_clauses": [], "unmarked_new": [], "matched_loosely": [], "table_rows": []}
        self.res = resolutions
        self.touched = []  # base spans the proposal speaks for (for the rename and the checks)

    # ---- resolutions
    def resolution(self, kind, cid, idx):
        for r in self.res:
            if r[0] == kind and r[1] == cid and r[2] == str(idx):
                return r
        return None

    def refuse(self, cid, idx, msg, old=None, base=None):
        d = ""
        if old is not None and base is not None:
            d = "\n".join(difflib.unified_diff(
                [l.strip() for l in base.split("\n") if l.strip()],
                [l.strip() for l in old.split("\n") if l.strip()],
                "base", "proposal's old text (<ins> dropped, <del> kept)", lineterm="", n=1))
        self.refusals.append({"clause": cid, "block": idx, "message": msg, "diff": d})

    # ---- main
    def run(self):
        for top in self.ptree.children:
            self.merge_clause(top)
        return self

    def merge_clause(self, p):
        if p.id and p.id.startswith("del-"):
            target = p.id[4:]
            b = self.bid.get(target)
            if b is None:
                self.refuse(p.id, "-", f"del- clause: base has no clause {target}")
                return
            self.edit_remove_clause(b, f"removed by {p.id}")
            return
        b = self.bid.get(p.id)
        if b is None:
            self.refuse(p.id, "-", "top-level proposal clause not in base")
            return
        if b.parent and p.parent and p.parent.id and b.parent.id != p.parent.id:
            self.log["moved_or_reordered"].append(f"{p.id}: proposal parent {p.parent.id}, base parent {b.parent.id}")
        # a clause whose h1 is wholly deleted: remove it
        pblocks = self.own_blocks(self.prop, p)
        h1 = next((x for x in pblocks if x[2] == "h1"), None)
        if h1 is not None:
            h1t = self.prop[h1[0]:h1[1]]
            if has_markup(h1t) and emptyish(resolve(h1t, "new")):
                self.check_deleted_clause(p, b)
                return
        self.merge_attrs(p, b)
        self.merge_own(p, b, pblocks)
        self.merge_children(p, b)

    def merge_attrs(self, p, b):
        """A proposal clause's attributes the base clause lacks (oldids): added to its tag. `number=` is the
        proposal's own section numbering, not an attribute of the base."""
        pa = dict(re.findall(r'(\w[\w-]*)="([^"]*)"', p.attrs))
        ba = dict(re.findall(r'(\w[\w-]*)="([^"]*)"', b.attrs))
        for k, v in pa.items():
            if k in ("number", "id"):
                continue
            if k == "oldids":
                have = set(ba.get("oldids", "").split(",")) - {""}
                add = [x for x in v.split(",") if x not in have]
                if not add:
                    continue
                tag = self.base[b.open_start:b.open_end]
                if "oldids=" in tag:
                    nt = re.sub(r'oldids="([^"]*)"', lambda m, add=add: f'oldids="{m.group(1)},{",".join(add)}"', tag)
                else:
                    nt = tag.replace(f'id="{b.id}"', f'id="{b.id}" oldids="{",".join(add)}"')
                self.edits.append((b.open_start, b.open_end, nt, f"{b.id}: oldids {add}"))
                self.log["attrs"].append(f"{b.id}: oldids + {add}")
            elif ba.get(k) != v:
                self.log["attrs"].append(f"{b.id}: proposal {k}={v!r}, base {ba.get(k)!r} (base kept)")

    def own_blocks(self, text, node):
        out = []
        for s, e in node.own_segments():
            out.extend(blocks(text, s, e))
        return out

    def check_deleted_clause(self, p, b):
        old = resolve(self.prop[p.open_start:p.close_end], "old")
        base = self.base[b.open_start:b.close_end]
        if norm(old) != norm(base):
            # the proposal may reproduce only part; compare its own blocks as a subsequence
            bb = [norm(self.base[s:e]) for s, e, k in self.own_blocks(self.base, b)]
            missing = [norm(resolve(self.prop[s:e], "old")) for s, e, k in self.own_blocks(self.prop, p)
                       if norm(resolve(self.prop[s:e], "old")) not in bb]
            if missing:
                self.refuse(p.id, "-", "deleted clause: its old text differs from the base", old, base)
                return
        self.edit_remove_clause(b, f"{p.id}: h1 deleted")

    def edit_remove_clause(self, b, why):
        s = self.base.rfind("\n", 0, b.open_start)  # with its line and the blank line before it
        e = b.close_end
        if self.base[s - 1:s] == "\n":
            s -= 1
        self.edits.append((s, e, "", why))
        self.touched.append((b.open_start, b.close_end))
        self.log["removed"].append(b.id)

    def merge_own(self, p, b, pblocks):
        bblocks = self.own_blocks(self.base, b)
        bnorm = [norm(self.base[s:e]) for s, e, k in bblocks]
        last = -1  # index of the last matched base block
        matched = {}  # proposal idx -> base idx
        pending = []  # inserted blocks waiting for their place check
        cid = p.id
        did_something = False
        for i, (s, e, kind) in enumerate(pblocks):
            if kind == "#comment":
                self.log["ignored_comments"] += 1
                continue
            raw = self.prop[s:e]
            old, new = resolve(raw, "old"), resolve(raw, "new")
            if kind == "emu-grammar" and 'type="definition"' in raw[:60]:
                j = self.merge_grammar(cid, i, raw, bblocks, last)
                if j is not None:
                    last = j
                    matched[i] = j
                continue
            r = self.resolution("ignore", cid, i)
            if r:
                self.log["resolved"].append(" ".join(r))
                continue
            if kind == "emu-note" and 'type="editor"' in raw[:40]:
                self.log["editor_notes_dropped"].append(f"{cid} block {i}")
                continue
            if (not has_markup(raw) and kind == "emu-grammar" and i + 1 < len(pblocks)
                    and pblocks[i + 1][2] == "emu-alg" and has_markup(self.prop[pblocks[i + 1][0]:pblocks[i + 1][1]])
                    and emptyish(resolve(self.prop[pblocks[i + 1][0]:pblocks[i + 1][1]], "old"))
                    and norm(old) not in bnorm[last + 1:]):
                # an SDO row whose steps are all <ins> but whose grammar is not marked: new
                self.log["unmarked_new"].append(f"{cid} block {i}: {norm(old)[:90]}")
                old = ""
            if emptyish(old) and has_markup(raw) or old == "":
                # an insertion; already upstream?
                nn = norm(new)
                j = next((k for k in range(last + 1, len(bblocks)) if bnorm[k] == nn), None)
                if j is not None:
                    self.log["already"].append(f"{cid} block {i} ({kind}) already in base")
                    last = j
                    matched[i] = j
                    continue
                gap = self.prop[pblocks[i - 1][1]:s] if i > 0 else "\n"
                gap = "\n" * max(1, gap.count("\n"))
                pending.append((i, kind, new, last, s, gap))
                continue
            on = norm(old)
            j = next((k for k in range(last + 1, len(bblocks)) if bnorm[k] == on), None)
            if j is None:
                lo = loose(old)
                j = next((k for k in range(last + 1, len(bblocks)) if loose(self.base[bblocks[k][0]:bblocks[k][1]]) == lo), None)
                if j is not None:
                    self.log["matched_loosely"].append(f"{cid} block {i} ({kind})")
            if j is None and kind == "emu-table":
                j = self.merge_table(cid, i, raw, bblocks, last)
                if j is not None:
                    last = j
                    matched[i] = j
                    did_something = True
                    continue
            if j is None:
                # already applied upstream?
                nn = norm(new)
                j2 = next((k for k in range(last + 1, len(bblocks)) if bnorm[k] == nn), None)
                if j2 is not None and has_markup(raw):
                    self.log["already"].append(f"{cid} block {i} ({kind}) already in base")
                    last = j2
                    matched[i] = j2
                    continue
                # resolutions
                cand = self.best_candidate(on, kind, bblocks, bnorm, last)
                rb = self.resolution("rebase", cid, i) or self.resolution("rebase-take", cid, i)
                if cand is not None and rb:
                    bs, be, _ = bblocks[cand]
                    t, notes = self.rebase(old, new, self.base[bs:be], take=rb[0] == "rebase-take",
                                           delta=line_indent(self.base, bs) - line_indent(self.prop, s))
                    if t is None:
                        self.refuse(cid, i, "rebase: " + "; ".join(notes))
                    else:
                        self.edits.append((bs, be, t, f"{cid} block {i} rebased"))
                        self.touched.append((bs, be))
                        self.log["blocks_replaced"].append(f"{cid}#{i} {kind} (rebased)")
                        self.log["resolved"].append(" ".join(rb) + (" | " + "; ".join(notes) if notes else ""))
                    last = cand
                    matched[i] = cand
                    did_something = True
                    continue
                ru = self.resolution("use-new", cid, i)
                rk = self.resolution("keep-base", cid, i)
                rp = [r for r in self.res if r[0] == "patch" and r[1] == cid and r[2] == str(i)]
                if cand is not None and (ru or rk or rp):
                    bs, be, _ = bblocks[cand]
                    if ru:
                        self.replace_block(cid, i, kind, bs, be, s, new, "use-new")
                        self.log["resolved"].append(" ".join(ru))
                    elif rp:
                        t = self.base[bs:be]
                        for r in rp:
                            o, n = r[3], r[4]
                            if t.count(o) != 1:
                                self.refuse(cid, i, f"patch: {o!r} occurs {t.count(o)} times in the base block")
                                break
                            t = t.replace(o, n)
                        else:
                            self.edits.append((bs, be, t, f"{cid} block {i} patched"))
                            self.touched.append((bs, be))
                            self.log["blocks_replaced"].append(f"{cid}#{i} {kind} (patched)")
                            for r in rp:
                                self.log["resolved"].append(" ".join(r[:3]) + f" {r[3]!r} ==> {r[4]!r}")
                    else:
                        self.log["resolved"].append(" ".join(rk))
                    last = cand
                    matched[i] = cand
                    did_something = True
                    continue
                if not has_markup(raw):
                    msg = "context block (no markup) differs from the base"
                else:
                    msg = "old text (<ins> dropped, <del> kept) differs from the base"
                self.refuse(cid, i, f"{msg}; kind {kind}" + ("" if cand is None else f"; nearest base block {cand}"),
                            old, self.base[bblocks[cand][0]:bblocks[cand][1]] if cand is not None else "")
                continue
            last = j
            matched[i] = j
            if has_markup(raw):
                bs, be, _ = bblocks[j]
                self.replace_block(cid, i, kind, bs, be, s, new, "replace")
                did_something = True
            else:
                self.log["context_ok"] += 1
        # place pending insertions
        mvals = sorted(matched.items())
        for i, kind, new, prev, ps, gap in pending:
            nxt = next((bj for pi, bj in mvals if pi > i), None)
            gap_end = nxt if nxt is not None else len(bblocks)
            omitted = list(range(prev + 1, gap_end))
            r = self.resolution("place", cid, i)
            if r:
                after = int(r[4])
                self.insert_block_after(cid, i, kind, bblocks[after][1], new, ps, gap)
                self.log["resolved"].append(" ".join(r))
                continue
            if omitted:
                kinds = ", ".join(f"{k}:{bblocks[k][2]}" for k in omitted)
                self.refuse(cid, i, f"inserted {kind}: the proposal omits base blocks here ({kinds}); "
                            f"say where with `place {cid} {i} after N`")
                continue
            anchor = bblocks[prev][1] if prev >= 0 else self.base.find(">", b.open_start) + 1
            self.insert_block_after(cid, i, kind, anchor, new, ps, gap)
        self.touched.append((b.open_start, b.close_end))
        if did_something or pending:
            self.log["replaced"].append(cid)

    def rebase(self, old, new, base, take, delta):
        """A three-way merge by lines: the proposal's change old->new applied to the base block.
        Lines are matched old<->base loosely (white space, punctuation); old->new compares indentation too.
        `take`: where an unchanged old line differs from its base line, the proposal's line wins (it changed
        the text without marking it); otherwise the base's wins and the difference is reported."""
        O, N, B = old.split("\n"), new.split("\n"), base.split("\n")
        ko = [loose(l) for l in O]
        kb = [loose(l) for l in B]
        ob = {}
        sm = difflib.SequenceMatcher(None, ko, kb, autojunk=False)
        notes = []
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                for d in range(i2 - i1):
                    ob[i1 + d] = j1 + d
            elif tag == "replace" and i2 - i1 == j2 - j1:
                for d in range(i2 - i1):
                    ob[i1 + d] = j1 + d
            if tag != "equal":
                notes.append(f"base differs from the proposal's old text: {tag} old {[O[k].strip() for k in range(i1, i2)]} base {[B[k].strip() for k in range(j1, j2)]}")
        out = {}  # base index -> replacement lines (list); 'ins_after' base index -> lines
        ins_after = {}
        drop = set()
        ind = lambda l: (" " * delta + l) if delta >= 0 else l[min(-delta, len(l) - len(l.lstrip(" "))):]
        cn = difflib.SequenceMatcher(None, O, N, autojunk=False)
        newn = set()
        for tag, i1, i2, j1, j2 in cn.get_opcodes():
            if tag != "equal":
                newn.update(range(j1, j2))
        def indent(l):
            return len(l) - len(l.lstrip(" "))
        def parent(j):
            for k in range(j - 1, -1, -1):
                if N[k].strip() and indent(N[k]) < indent(N[j]):
                    return k
            return None
        for tag, i1, i2, j1, j2 in cn.get_opcodes():
            if tag == "equal":
                for d in range(i2 - i1):
                    k, j = ob.get(i1 + d), j1 + d
                    pj = parent(j)
                    if k is not None and pj in newn and indent(N[j]) + delta != indent(B[k]):
                        # the proposal nests this line under a line it inserts
                        out[k] = [ind(N[j])]
                        notes.append(f"re-nested under an inserted line: {N[j].strip()[:60]}")
                if take:
                    for d in range(i2 - i1):
                        k = ob.get(i1 + d)
                        if k is not None and O[i1 + d].strip() != B[k].strip():
                            out[k] = [ind(N[j1 + d])]
                continue
            rng = list(range(i1, i2))
            if any(k not in ob for k in rng):
                return None, notes + [f"conflict: the lines the proposal changes are not all in the base: {[O[k].strip() for k in rng if k not in ob]}"]
            bl = [ob[k] for k in rng]
            if bl and bl != list(range(bl[0], bl[0] + len(bl))):
                return None, notes + ["conflict: the changed lines are not contiguous in the base"]
            newl = [ind(l) for l in N[j1:j2]]
            if bl:
                out[bl[0]] = newl
                drop.update(bl[1:])
            else:
                # pure insertion before old line i1: after base line ob[i1-1] (must be adjacent to ob[i1])
                prev = ob.get(i1 - 1)
                nxt = ob.get(i1)
                if prev is None or (nxt is not None and nxt != prev + 1):
                    if nxt is not None and prev is None:
                        ins_after.setdefault(nxt - 1, []).extend(newl)
                        continue
                    return None, notes + [f"conflict: insertion point is ambiguous in the base ({[l.strip() for l in N[j1:j2]]})"]
                ins_after.setdefault(prev, []).extend(newl)
        res = []
        for k, l in enumerate(B):
            if k in drop:
                pass
            elif k in out:
                res.extend(out[k])
            else:
                res.append(l)
            if k in ins_after:
                res.extend(ins_after[k])
        if -1 in ins_after:
            res = ins_after[-1] + res
        return "\n".join(res), notes

    def best_candidate(self, on, kind, bblocks, bnorm, last):
        best, score = None, 0.0
        for k in range(last + 1, len(bblocks)):
            if bblocks[k][2] != kind:
                continue
            sc = difflib.SequenceMatcher(None, on, bnorm[k], autojunk=False).ratio()
            if sc > score:
                best, score = k, sc
        return best if score > 0.5 else None

    def replace_block(self, cid, i, kind, bs, be, ps, new, how):
        delta = line_indent(self.base, bs) - line_indent(self.prop, ps)
        t = reindent(new, delta)
        if emptyish(t):
            # the whole block goes: take its line too
            ls = bs
            while ls > 0 and self.base[ls - 1].isspace():
                ls -= 1
            self.edits.append((ls, be, "", f"{cid} block {i} removed"))
            self.log["blocks_removed"].append(f"{cid}#{i} {kind}")
        else:
            self.edits.append((bs, be, t, f"{cid} block {i} {how}"))
            self.log["blocks_replaced"].append(f"{cid}#{i} {kind}")
        self.touched.append((bs, be))

    def insert_block_after(self, cid, i, kind, anchor, new, ps=None, gap="\n"):
        ind = line_indent(self.base, anchor)
        delta = ind - (line_indent(self.prop, ps) if ps is not None else ind)
        t = reindent(new.strip("\n"), delta)
        self.edits.append((anchor, anchor, gap + " " * ind + t, f"{cid} block {i} inserted"))
        self.log["blocks_inserted"].append(f"{cid}#{i} {kind}")

    def merge_table(self, cid, i, raw, bblocks, last):
        """A table whose old text differs from the base's as a whole: merge it row by row (the base may have
        gained a <thead> or other rows). Every old row must be a base row; changed rows are replaced, new rows
        go after the row before them."""
        TR = re.compile(r"<tr\b[^>]*>.*?</tr>", re.S)
        cands = [k for k in range(last + 1, len(bblocks)) if bblocks[k][2] == "emu-table"]
        pid = re.search(r'\bid="([^"]*)"', raw[:200])
        for k in cands:
            bs, be, _ = bblocks[k]
            bt = self.base[bs:be]
            bid = re.search(r'\bid="([^"]*)"', bt[:200])
            if pid and bid and pid.group(1) != bid.group(1):
                continue
            brows = [(m.start() + bs, m.end() + bs, loose(m.group(0))) for m in TR.finditer(bt)]
            prows = [m.group(0) for m in TR.finditer(raw)]
            edits, prev, ok = [], None, True
            for pr in prows:
                o, n = resolve(pr, "old"), resolve(pr, "new")
                if emptyish(re.sub(r"<tr\b[^>]*>|</tr>|<t[dh]\b[^>]*>|</t[dh]>", "", o)):
                    if prev is None:
                        ok = False
                        break
                    edits.append((prev[1], prev[1], "\n" + " " * line_indent(self.base, prev[0]) + n.strip(), "row added"))
                    self.log["table_rows"].append(f"{cid}#{i}: row added")
                    continue
                lo = loose(o)
                hit = next((r for r in brows if r[2] == lo), None)
                if hit is None:
                    ok = False
                    break
                if has_markup(pr):
                    edits.append((hit[0], hit[1], n.strip(), "row changed"))
                    self.log["table_rows"].append(f"{cid}#{i}: row changed")
                prev = hit
            if ok:
                for e in edits:
                    self.edits.append((e[0], e[1], e[2], f"{cid} block {i} {e[3]}"))
                self.touched.append((bs, be))
                self.log["blocks_replaced"].append(f"{cid}#{i} emu-table (row by row)")
                return k
        return None

    def merge_grammar(self, cid, i, raw, bblocks, last):
        """Merge a definition grammar rule by rule; returns the base block index used, or None."""
        inner = lambda t: t[t.index(">") + 1:t.rindex("</emu-grammar>")]
        old_rules = grammar_rules(resolve(inner(raw), "old"))
        new_rules = grammar_rules(resolve(inner(raw), "new"))
        cands = [k for k in range(len(bblocks)) if bblocks[k][2] == "emu-grammar"
                 and 'type="definition"' in self.base[bblocks[k][0]:bblocks[k][0] + 60]]
        if not cands:
            self.refuse(cid, i, "definition grammar: base clause has none")
            return None
        old_by = {l: t for l, t in old_rules if l}
        used = None
        for lhs, ntext in new_rules + [(l, None) for l, t in old_rules if l not in {x for x, _ in new_rules}]:
            otext = old_by.get(lhs)
            for k in cands:
                bs, be, _ = bblocks[k]
                btext = self.base[bs:be]
                brules = grammar_rules(inner(btext))
                hit = [t for l, t in brules if l == lhs]
                if hit or (otext is None and k == cands[0]):
                    break
            else:
                hit = []
            if otext is not None and not hit:
                self.refuse(cid, i, f"definition grammar: rule {lhs} not in the base")
                continue
            if otext is not None and norm(hit[0]) != norm(otext):
                if ntext is not None and norm(hit[0]) == norm(ntext):
                    self.log["already"].append(f"{cid} grammar {lhs} already in base")
                    used = k
                    continue
                self.refuse(cid, i, f"definition grammar: rule {lhs} differs from the base", otext, hit[0])
                continue
            used = k
            if ntext is not None and otext is not None and norm(ntext) == norm(otext):
                self.log["context_ok"] += 1
                continue
            bstart = self.base.index("\n" + hit[0], bs) + 1 if hit else None
            if ntext is None:  # rule deleted
                self.edits.append((self.base.rfind("\n", 0, bstart) - 0, bstart + len(hit[0]), "", f"{cid} rule {lhs} removed"))
                self.log["grammar_rules"].append(f"{cid}: {lhs} removed")
                continue
            # re-indent the proposal rule to the base's
            pl = [l for l in ntext.split("\n") if l.strip()]
            pind = len(pl[0]) - len(pl[0].lstrip())
            if hit:
                bind = len(hit[0]) - len(hit[0].lstrip())
                t = "\n".join(" " * bind + l[pind:] for l in pl)
                self.edits.append((bstart, bstart + len(hit[0]), t, f"{cid} rule {lhs} replaced"))
                # bstart points at the rule's first char including indentation? index() of the whole text: yes
                self.log["grammar_rules"].append(f"{cid}: {lhs} changed")
            else:
                # a new rule: after the rule that precedes it in the proposal
                names = [l for l, _ in new_rules]
                prev = names[names.index(lhs) - 1] if names.index(lhs) > 0 else None
                brules = grammar_rules(inner(self.base[bblocks[k][0]:bblocks[k][1]]))
                ph = [t for l, t in brules if l == prev]
                if not ph:
                    self.refuse(cid, i, f"definition grammar: new rule {lhs}: its predecessor {prev} is not in the base")
                    continue
                pstart = self.base.index("\n" + ph[0], bblocks[k][0]) + 1
                bind = len(ph[0]) - len(ph[0].lstrip())
                t = "\n".join(" " * bind + l[pind:] for l in pl)
                # the predecessor may itself be replaced: insert at its end
                self.edits.append((pstart + len(ph[0]), pstart + len(ph[0]), "\n\n" + t, f"{cid} rule {lhs} added"))
                self.log["grammar_rules"].append(f"{cid}: {lhs} added after {prev}")
        return used

    def merge_children(self, p, b):
        kids = p.children
        for n, c in enumerate(kids):
            if c.id and (c.id in self.bid or c.id.startswith("del-")):
                self.merge_clause(c)
                continue
            # a new clause
            prev = next((k for k in reversed(kids[:n]) if k.id in self.bid), None)
            nxt = next((k for k in kids[n + 1:] if k.id in self.bid), None)
            text = self.resolve_clause(c)
            om = re.search(r'oldids="([^"]*)"', c.attrs)
            for oid in (om.group(1).split(",") if om else []):
                if oid in self.bid:
                    ob = self.bid[oid]
                    alg = lambda t: [norm(x) for x in re.findall(r"<emu-alg>(.*?)</emu-alg>", t, re.S)]
                    same = alg(self.base[ob.open_start:ob.close_end]) == alg(text)
                    self.log["renamed_clauses"].append(f"{oid} -> {c.id}: steps {'identical' if same else 'DIFFER'}")
            if prev is not None:
                bp = self.bid[prev.id]
                anchor, ind = bp.close_end, line_indent(self.base, bp.open_start)
                where = f"after {prev.id}"
                txt = "\n\n" + " " * ind + reindent(text, ind - line_indent(self.prop, c.open_start))
            elif nxt is not None:
                bn = self.bid[nxt.id]
                ls = self.base.rfind("\n", 0, bn.open_start) + 1
                anchor, ind = ls, line_indent(self.base, bn.open_start)
                where = f"before {nxt.id}"
                txt = " " * ind + reindent(text, ind - line_indent(self.prop, c.open_start)) + "\n\n"
            else:
                # end of the parent: before its closing tag line
                ls = self.base.rfind("\n", 0, b.close_start)
                ind = line_indent(self.base, b.open_start) + 2
                anchor = ls
                where = f"last child of {b.id}"
                txt = "\n\n" + " " * ind + reindent(text, ind - line_indent(self.prop, c.open_start))
            self.edits.append((anchor, anchor, txt, f"new clause {c.id} {where}"))
            self.log["inserted"].append(f"{c.id} ({where})")
            # its new sub-clauses travel with it
            for d in c.walk():
                if d is not c and d.id:
                    self.log["inserted"].append(f"  {d.id} (inside {c.id})")

    def resolve_clause(self, c):
        return resolve(self.prop[c.open_start:c.close_end], "new")

    def apply_renames(self, out):
        for r in self.res:
            if r[0] != "rename":
                continue
            old, new = r[1], r[2]
            n = len(re.findall(r"\b" + re.escape(old) + r"\b", out))
            out = re.sub(r"(?<![\w-])" + re.escape(old) + r"\b(?!-)", new, out)
            self.log["renamed"].append(f"{old} -> {new}: {n} occurrence(s) left by the proposal")
        return out

    def output(self):
        edits = sorted(self.edits, key=lambda e: (e[0], e[1]))
        for a, b in zip(edits, edits[1:]):
            if a[1] > b[0] and not (a[0] == a[1] == b[0]):
                raise SystemExit(f"overlapping edits: {a[3]} / {b[3]}")
        out, pos = [], 0
        for s, e, t, _ in edits:
            out.append(self.base[pos:s])
            out.append(t)
            pos = e
        out.append(self.base[pos:])
        return "".join(out)


def read_resolutions(path):
    res = []
    if not path:
        return res
    with open(path, encoding="utf-8") as f:
        lines = f.read().splitlines()
    for line in lines:
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if line.startswith("patch "):
            head, rest = line[6:].split(" ", 2)[:2], line[6:].split(" ", 2)[2]
            old, new = rest.split(" ==> ", 1)
            res.append(["patch", head[0], head[1], json.loads(old), json.loads(new)])
        else:
            res.append(line.split())
    return res


def checks(m, out, base, prop):
    """Every <ins> text is in the output; no <del> text is, unless the base has it outside the proposal's spans;
    the clause tree is the base's less the removed plus the inserted, in place."""
    rep = {}
    nout = norm(out)
    ins = [norm(re.sub(r"<(?:ins|del)\b[^>]*>|</(?:ins|del)>", "", x)) for x in INS.findall(prop)]
    ins_missing = [x for x in ins if x and x not in nout]
    rep["ins_total"], rep["ins_missing"] = len(ins), ins_missing
    dels = [norm(x) for x in DEL.findall(prop)]
    nbase = norm(base)
    nnew = norm(resolve(prop, "new"))
    left = []
    for d in dels:
        if not d or len(d) < 12:
            continue
        if nout.count(d) > 0 and nout.count(d) >= nbase.count(d) and d not in nnew:
            left.append(d)
    rep["del_total"], rep["del_left"] = len(dels), left
    bt, ot = parse_tree(base), parse_tree(out)
    bids = [n.id for n in bt.walk() if n.id]
    oids = [n.id for n in ot.walk() if n.id]
    removed = set()
    for rid in m.log["removed"]:
        removed |= {d.id for d in m.bid[rid].walk() if d.id}
    inserted = [s.split()[0] for s in m.log["inserted"]]
    rep["clauses_base"], rep["clauses_out"] = len(bids), len(oids)
    rep["tree_ok"] = [i for i in oids if i not in set(inserted)] == [i for i in bids if i not in removed] \
        and set(oids) - set(bids) == set(inserted)
    # parents of the inserted
    par = {}
    for n in ot.walk():
        for c in n.children:
            par[c.id] = n.id
    rep["inserted_parents"] = {i: par.get(i) for i in inserted}
    return rep


def clause_name(text, node):
    """The name an abstract operation's clause defines: its `aoid`, else its h1 up to `(`, if that is one word."""
    m = re.search(r'\baoid="([^"]*)"', node.attrs)
    if m:
        return m.group(1)
    h = re.search(r"<h1>(.*?)</h1>", text[node.open_end:node.close_end], re.S)
    if not h:
        return None
    t = re.sub(r"<[^>]+>", "", h.group(1)).strip()
    t = re.sub(r"^\S+\s+", "", t) if re.match(r"^(Static|Runtime) Semantics:", t) else t
    w = t.split("(")[0].strip()
    return w if re.fullmatch(r"[A-Za-z][\w.%]*", w) and "(" in t else None


def warnings(m, base, out):
    """Names the proposal removes or renames that the result still uses where the proposal did not show them: an
    abstract operation's name (of a removed clause, or of a base clause another takes over by `oldids`) not
    answered by a `rename`, and a link (`href="#id"`) to a removed clause that no clause of the result names in
    its `oldids`."""
    renamed = {r[1] for r in m.res if r[0] == "rename"}
    ot = parse_tree(out)
    out_ids = {n.id for n in ot.walk() if n.id}
    oldids = set()
    for n in ot.walk():
        om = re.search(r'oldids="([^"]*)"', n.attrs)
        if om:
            oldids |= set(om.group(1).split(","))
    gone = []  # (base node, why)
    for rid in m.log["removed"]:
        for d in m.bid[rid].walk():
            if d.id:
                gone.append((d, f"removed ({rid})"))
    for n in ot.walk():
        om = re.search(r'oldids="([^"]*)"', n.attrs)
        for oid in (om.group(1).split(",") if om else []):
            b = m.bid.get(oid)
            if b is not None and oid not in out_ids:
                new = clause_name(out, n)
                if new and clause_name(base, b) not in (None, new):
                    gone.append((b, f"renamed {new} ({n.id} oldids)"))
    warn = []
    seen = set()
    for b, why in gone:
        name = clause_name(base, b)
        if name and name not in renamed and name not in seen and not any(name == clause_name(out, n) for n in ot.walk()):
            seen.add(name)
            where = sorted({n.id for n in ot.walk() if n.id and re.search(r"(?<![\w-])" + re.escape(name) + r"\b(?!-)",
                                                                       "".join(out[s:e] for s, e in n.own_segments()))})
            if where:
                warn.append(f"{name} ({b.id}, {why}) is still used in {len(where)} clause(s): {', '.join(where[:8])}"
                            f"{' …' if len(where) > 8 else ''}; answer with `rename {name} NEW` if the proposal renames it")
        if b.id not in out_ids and b.id not in oldids:
            n = out.count(f'href="#{b.id}"')
            if n:
                warn.append(f'href="#{b.id}" ({why}) is still linked {n} time(s), and no clause of the result has it in its oldids')
    return warn


def copy_images(prop_dir, out_dir, out, base_dir=None):
    """The proposal's figures the result uses (`img/NAME`) that the base lacks, copied from PROPOSAL/img to OUT's
    img/. A figure the base has stays the base's: a proposal's copy of it is the base's file as the proposal found
    it (a warning when the two differ). One the result uses that neither has is a warning. The names copied, and
    the problems."""
    import shutil
    from pathlib import Path
    copied, problems = [], []
    for name in sorted(set(re.findall(r'(?:src|href|data)="img/([^"#?]+)"', out))):
        src = Path(prop_dir) / "img" / name
        have = Path(base_dir) / "img" / name if base_dir else None
        if not src.exists():
            if not (have and have.exists()):
                problems.append(f"img/{name}: the result uses it; neither the proposal nor the base has it")
            continue
        if have and have.exists():
            if have.read_bytes() != src.read_bytes():
                problems.append(f"img/{name}: the proposal's copy differs from the base's; the base's is kept")
            continue
        dst = Path(out_dir) / "img" / name
        dst.parent.mkdir(parents=True, exist_ok=True)
        if not dst.exists() or dst.read_bytes() != src.read_bytes():
            shutil.copyfile(src, dst)
        copied.append(name)
    return copied, problems


def copy_imports(base_dir, out_dir, out):
    """The files the result imports (`<emu-import href="F">`), copied from beside the base to beside OUT where they
    are not there already (the generators read them from beside spec.html)."""
    import shutil
    from pathlib import Path
    copied = []
    if Path(base_dir).resolve() == Path(out_dir).resolve():
        return copied
    for name in sorted(set(re.findall(r'<emu-import href="([^"]+)"', out))):
        src, dst = Path(base_dir) / name, Path(out_dir) / name
        if src.exists() and (not dst.exists() or dst.read_bytes() != src.read_bytes()):
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)
            copied.append(name)
    return copied


def merge(base, prop, resolutions):
    """The result of applying `prop` (a spec.emu's text) to `base` (a spec.html's text), and the report: its log,
    refusals, warnings and checks. `resolutions` is `read_resolutions`'s list."""
    m = Merger(base, prop, resolutions).run()
    out = m.apply_renames(m.output())
    rep = {"log": m.log, "refusals": m.refusals, "warnings": warnings(m, base, out)}
    rep["checks"] = checks(m, out, base, prop)
    return out, rep


def main():
    import os
    import subprocess
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("base", help="the base spec.html")
    ap.add_argument("proposal", help="the proposal's spec.emu, or its directory")
    ap.add_argument("out", help="the spec.html to write")
    ap.add_argument("--resolutions", help="the answers to the merge's questions")
    ap.add_argument("--report", help="write the log, refusals, warnings and checks here as JSON")
    ap.add_argument("--force", action="store_true", help="write the output even with refusals (for inspection)")
    ap.add_argument("--check", metavar="SPEC-GEN", help="run this spec-gen's round trip on the result")
    ap.add_argument("--overlay", help="the overlay for --check (default: spec/formal)")
    a = ap.parse_args()
    prop_path = os.path.join(a.proposal, "spec.emu") if os.path.isdir(a.proposal) else a.proposal
    with open(a.base, encoding="utf-8") as f:
        base = f.read()
    with open(prop_path, encoding="utf-8") as f:
        prop = f.read()
    out, rep = merge(base, prop, read_resolutions(a.resolutions))
    for r in rep["refusals"]:
        print(f"REFUSED {r['clause']} block {r['block']}: {r['message']}")
        if r["diff"]:
            print("    " + r["diff"].replace("\n", "\n    "))
    for w in rep["warnings"]:
        print(f"warning: {w}")
    refused = len(rep["refusals"])
    if not refused or a.force:
        copied, problems = copy_images(os.path.dirname(prop_path), os.path.dirname(os.path.abspath(a.out)), out,
                                       os.path.dirname(os.path.abspath(a.base)))
        rep["images"] = copied
        rep["imports"] = copy_imports(os.path.dirname(os.path.abspath(a.base)), os.path.dirname(os.path.abspath(a.out)), out)
        for p in problems:
            print(p if p.startswith("refused") else f"warning: {p}")
        refused += sum(p.startswith("refused") for p in problems)
    if a.report:
        with open(a.report, "w", encoding="utf-8") as f:
            json.dump(rep, f, indent=1, ensure_ascii=False)
    if refused and not a.force:
        print(f"{refused} refusal(s); nothing written")
        return 1
    with open(a.out, "w", encoding="utf-8") as f:
        f.write(out)
    c, log = rep["checks"], rep["log"]
    ok = not c["ins_missing"] and not c["del_left"] and c["tree_ok"]
    print(f"written {a.out}: {len(log['replaced'])} clauses changed, {len(log['inserted'])} inserted, "
          f"{len(log['removed'])} removed, {len(rep.get('images', []))} figures; <ins> missing {len(c['ins_missing'])}, "
          f"<del> left {len(c['del_left'])}, clause tree {'as expected' if c['tree_ok'] else 'NOT as expected'}; "
          f"{len(rep['warnings'])} warning(s)")
    if a.check:
        ov = a.overlay or os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "spec", "formal")
        r = subprocess.run([a.check, f"--spec={a.out}", f"--overlay={ov}", "roundtrip"], capture_output=True, text=True, check=False)
        tail = [l for l in r.stdout.splitlines() if " differ " in l]
        print(f"spec-gen roundtrip: {'ok' if r.returncode == 0 else 'FAILED'}; " + "; ".join(tail))
        if r.returncode != 0:
            print(r.stderr[-2000:])
            return 1
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
