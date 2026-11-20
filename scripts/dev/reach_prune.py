"""Delete the declarations dead.all.tsv lists whose source range meets no live declaration's.

usage: reach_prune.py [--dry]   (run in the directory reach_combine.py wrote dead.all.tsv and live.all.tsv to)

A dead declaration is kept when:
- its range meets a live one's (a field of a live structure, a member of a mutual block with a live member);
- its head is no `def`/`theorem`/`structure`/`inductive`/`instance`/... (a macro, notation, `deriving` clause);
- its name is written in a line that is not deleted, outside its own range (a lemma a `simp [..]` or `rw [..]`
  names that the proof term does not show, an `rfl` lemma; a name a macro's expansion writes);
- it is a `@[simp]` theorem of the `rfl` kind (simp may use it without naming it in the term);
- ONLY (modules) excludes its module, or PROTECT (a regular expression) matches its name.
FORCE (a regular expression) overrides the textual rule for the names it matches (a name written only as another
declaration's, `call`, `init`). A `#print axioms x` (and its `#guard_msgs` message) goes with x.
Writes pruned.names (what it deleted) and kept.names (dead, kept by the textual or simp rule)."""
import re, sys, collections, os
from pathlib import Path
ROOT = Path("/Users/drcarney/src/ecma-formal/lean")
HEAD = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial|nonrec|public|scoped)\s+)*(def|abbrev|theorem|lemma|structure|inductive|opaque|initialize|class|instance)\b")
TOK = re.compile(r"[A-Za-z_][A-Za-z_0-9'!?]*(?:\.[A-Za-z_][A-Za-z_0-9'!?]*)*")
def rows(f):
    out = collections.defaultdict(list)
    for l in open(f):
        p = l.rstrip("\n").split("\t")
        if len(p) == 5: out[p[0]].append((int(p[1]), int(p[2]), p[3], p[4]))
    return out
ONLY = set(os.environ.get('ONLY', '').split())
PROTECT = re.compile(os.environ['PROTECT']) if os.environ.get('PROTECT') else None
FORCE = re.compile(os.environ['FORCE']) if os.environ.get('FORCE') else None
dead, live = rows("dead.all.tsv"), rows("live.all.tsv")

def last(n):
    # the name a source line writes: the last component, without Lean's private prefix
    return n.split(".")[-1]

files = {}
for p in ROOT.rglob("*.lean"):
    if "/Gen/" in str(p): continue
    files[".".join(p.relative_to(ROOT).with_suffix("").parts)] = p.read_text().split("\n")

# the candidates: (module, span, name, head line index)
cands = []
for mod, ds in sorted(dead.items()):
    if mod not in files: continue
    if ONLY and mod not in ONLY: continue
    lines = files[mod]
    lv = live.get(mod, [])
    blocks = []; st = []
    for i, l in enumerate(lines):
        if l.strip() == "mutual": st.append(i + 1)
        elif l.strip() == "end" and st:
            s0 = st.pop()
            if not st: blocks.append((s0, i + 1))
    for (a, b, kind, n) in ds:
        if kind == "ctor": continue
        if PROTECT and PROTECT.search(n): continue
        if any(not (lb < a or b < la) for (la, lb, _, _) in lv): continue
        i = a - 1
        if lines[i].lstrip().startswith("/--"):
            while i < b and "-/" not in lines[i]: i += 1
            i += 1
        if i >= len(lines) or not HEAD.match(lines[i]): continue
        if lines[i].lstrip().startswith("deriving"): continue
        span = (a, b)
        blk = [x for x in blocks if x[0] <= a and b <= x[1]]
        if blk:
            if any(not (lb < blk[0][0] or blk[0][1] < la) for (la, lb, _, _) in lv): continue
            span = blk[0]
        text = "\n".join(lines[i:b])
        if re.search(r"@\[[^\]]*\bsimp\b", lines[i]) and re.search(r":=\s*(by\s+)?rfl\s*$", text.strip()):
            continue
        cands.append((mod, span, n))

# the names written in each line
def code_lines(lines):
    """The lines without comments and string literals."""
    out = []; depth = 0
    for l in lines:
        s = []; i = 0; instr = False
        while i < len(l):
            c2 = l[i:i + 2]
            if depth:
                if c2 == "/-": depth += 1; i += 2
                elif c2 == "-/": depth -= 1; i += 2
                else: i += 1
            elif instr:
                if l[i] == "\\": i += 2
                else:
                    if l[i] == '"': instr = False
                    i += 1
            elif c2 == "/-": depth = 1; i += 2
            elif c2 == "--": break
            elif l[i] == '"': instr = True; i += 1
            else: s.append(l[i]); i += 1
        out.append("".join(s))
    return out

# `#print axioms x` (under `#guard_msgs` with its expected message): it goes with x, and is no use of it
PRINT = re.compile(r"^\s*(?:#guard_msgs\s+in\s+)?#print\s+axioms\s+(\S+)\s*$")
guards = collections.defaultdict(list)   # module -> [(first line, last line, name written)]
for mod, lines in files.items():
    for j, l in enumerate(lines):
        m = PRINT.match(l)
        if not m: continue
        a = j
        if a >= 1 and lines[a - 1].rstrip().endswith("-/"):
            k = a - 1
            while k >= 0 and not lines[k].lstrip().startswith("/-- info"): k -= 1
            if k >= 0: a = k
        guards[mod].append((a + 1, j + 1, m.group(1)))
guardline = {(mod, j) for mod, gs in guards.items() for (a, b, _) in gs for j in range(a, b + 1)}

occ = collections.defaultdict(set)   # last component -> {(module, line)}
for mod, lines in files.items():
    for j, code in enumerate(code_lines(lines)):
        # a namespace's or section's name is no use of a declaration
        if re.match(r"^\s*(namespace|end|section|open|export)\b", code): continue
        if (mod, j + 1) in guardline: continue
        for t in TOK.findall(code):
            occ[t.split(".")[-1]].add((mod, j + 1, t))

def refers(t, n):
    """Whether the written name t may be n: its last component is n's, and from its first capitalised component
    on (a namespace; a lower-case qualifier is a variable's dot notation) it is a suffix of n."""
    ps = t.split(".")
    k = next((i for i, p in enumerate(ps[:-1]) if p[:1].isupper() and len(p) > 2), None)
    if k is None: return True
    s = ".".join(ps[k:])
    return n == s or n.endswith("." + s)

keep = set()
while True:
    killed = collections.defaultdict(set)
    for (mod, (a, b), n) in cands:
        if n in keep: continue
        killed[mod].update(range(a, b + 1))
    changed = False
    for (mod, (a, b), n) in cands:
        if n in keep: continue
        for (m, j, tok) in occ.get(last(n), ()):
            if m == mod and a <= j <= b: continue
            if not refers(tok, n): continue
            if j in killed[m]: continue
            if FORCE and FORCE.search(n): continue
            keep.add(n); changed = True; break
    if not changed: break

total = 0; names = []
bymod = collections.defaultdict(set)
for (mod, span, n) in cands:
    if n in keep: continue
    bymod[mod].add(span); names.append(n)
    for (a, b, w) in guards.get(mod, ()):
        if last(w) == last(n) and refers(w, n): bymod[mod].add((a, b))
for mod, spans in sorted(bymod.items()):
    lines = files[mod]
    spans = sorted(s for s in spans if not any(o != s and o[0] <= s[0] and s[1] <= o[1] for o in spans))
    kill = set()
    for a, b in spans:
        kill.update(range(a - 1, b))
        # a blank line after the declaration goes with it
        if b < len(lines) and lines[b].strip() == "" and a >= 2 and lines[a - 2].strip() == "": kill.add(b)
    # a `set_option ... in` or `open ... in` whose command is deleted goes with it
    IN = re.compile(r"^\s*(set_option|open)\b.*\bin\s*$")
    for i in range(len(lines) - 1, -1, -1):
        if i in kill or not IN.match(lines[i]): continue
        j = i + 1
        while j < len(lines) and j in kill: j += 1
        if j >= len(lines) or lines[j].strip() == "" or lines[j].startswith("end") or (j > i + 1 and IN.match(lines[j]) and j in kill):
            kill.add(i)
    total += len(spans)
    print(f"{mod}: {len(spans)} declarations, {len(kill)} lines")
    if "--dry" not in sys.argv:
        path = ROOT / (mod.replace(".", "/") + ".lean")
        path.write_text("\n".join(l for i, l in enumerate(lines) if i not in kill))
print("total", total, "kept by name or simp", len(keep))
Path("pruned.names").write_text("\n".join(names) + "\n")
Path("kept.names").write_text("\n".join(sorted(keep)) + "\n")
