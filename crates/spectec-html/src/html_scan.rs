//! Scanner, template instantiator, step-tree parser, and lossless splicer for `spec.html`.

use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HtmlStep {
    pub depth: usize,
    pub attrs: Option<String>,
    pub text: String,
    pub cont: Vec<String>,
    pub kids: Vec<HtmlStep>,
}

#[derive(Clone, Debug)]
pub struct HtmlBlock {
    pub clause: String,
    pub clause_k: usize,
    pub span: (usize, usize),
    pub line: usize,
    pub text: String,
}

#[derive(Clone, Debug)]
pub struct HtmlAlg {
    pub clause: String,
    pub idx: usize,
    pub span: (usize, usize),
    pub line: usize,
    pub attrs: String,
    pub text: String,
    pub key_span: Option<(usize, usize)>,
    pub key_text: Option<String>,
    pub base: usize,
    pub close_indent: usize,
    pub steps: Vec<HtmlStep>,
}

#[derive(Clone, Debug)]
pub struct HtmlEq {
    pub clause: String,
    pub idx: usize,
    pub span: (usize, usize),
    pub line: usize,
    pub indent: usize,
    pub text: String,
    pub line_text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EarlyLayout {
    Inline,
    Block,
    Raw,
}

#[derive(Clone, Debug)]
pub struct HtmlEarly {
    pub clause: String,
    pub idx: usize,
    pub span: (usize, usize),
    pub line: usize,
    pub indent: usize,
    pub layout: EarlyLayout,
    pub text: String,
    pub body_text: String,
    pub keys: Vec<((usize, usize), String)>,
}

#[derive(Clone, Debug)]
pub struct ClauseInfo {
    pub id: String,
    pub start: usize,
    pub end: usize,
    pub h1: String,
}

pub struct HtmlSpec {
    pub src: String,
    pub clauses: Vec<ClauseInfo>,
    pub blocks: Vec<HtmlBlock>,
    pub algs: Vec<HtmlAlg>,
    pub alg_map: BTreeMap<(String, usize), usize>,
    pub eqs: Vec<HtmlEq>,
    pub eq_map: BTreeMap<(String, usize), usize>,
    pub early: Vec<HtmlEarly>,
    pub early_map: BTreeMap<(String, usize), usize>,
    pub example_algs: usize,
}

pub fn line_of(s: &str, pos: usize) -> usize {
    s[..pos].bytes().filter(|&b| b == b'\n').count() + 1
}

pub fn column(s: &str, pos: usize) -> usize {
    pos - s[..pos].rfind('\n').map_or(0, |n| n + 1)
}

fn attr(tag: &str, name: &str) -> Option<String> {
    let key = format!(" {name}=\"");
    let i = tag.find(&key)? + key.len();
    let j = tag[i..].find('"')? + i;
    Some(tag[i..j].to_string())
}

pub fn step_line(ln: &str) -> Option<(usize, Option<String>, String)> {
    let indent = ln.len() - ln.trim_start().len();
    let t = &ln[indent..];
    let rest = t.strip_prefix("1. ")?;
    if let Some(r) = rest.strip_prefix('[') {
        if let Some(e) = r.find(']') {
            let after = &r[e + 1..];
            let text = after.strip_prefix(' ').unwrap_or(after);
            return Some((indent, Some(r[..e].to_string()), text.to_string()));
        }
    }
    Some((indent, None, rest.to_string()))
}

pub fn step_tree(body: &str) -> Result<(usize, Vec<HtmlStep>, usize), String> {
    let lines: Vec<&str> = body.split('\n').collect();
    if lines.len() < 2 || !lines[0].is_empty() {
        return Err("an emu-alg body that does not start on a new line".into());
    }
    let last = lines[lines.len() - 1];
    if !last.chars().all(|c| c == ' ') {
        return Err("text before </emu-alg> on its line".into());
    }
    let close_indent = last.len();
    let mut roots: Vec<HtmlStep> = Vec::new();
    let mut base = None;
    let mut path: Vec<usize> = Vec::new();

    fn at<'a>(roots: &'a mut Vec<HtmlStep>, path: &[usize]) -> &'a mut HtmlStep {
        let mut s = &mut roots[path[0]];
        for &k in &path[1..] {
            s = &mut s.kids[k];
        }
        s
    }

    for ln in &lines[1..lines.len() - 1] {
        match step_line(ln) {
            Some((indent, attrs, text)) => {
                let b = *base.get_or_insert(indent);
                if indent < b || (indent - b) % 2 != 0 {
                    return Err(format!("irregular indentation: {ln:?}"));
                }
                let depth = (indent - b) / 2;
                if depth > path.len() {
                    return Err(format!("a step nested too deep: {ln:?}"));
                }
                path.truncate(depth);
                let st = HtmlStep {
                    depth,
                    attrs,
                    text,
                    cont: Vec::new(),
                    kids: Vec::new(),
                };
                if depth == 0 {
                    roots.push(st);
                    path.push(roots.len() - 1);
                } else {
                    let parent = at(&mut roots, &path);
                    parent.kids.push(st);
                    let k = parent.kids.len() - 1;
                    path.push(k);
                }
            }
            None => {
                if path.is_empty() {
                    return Err(format!("text before the first step: {ln:?}"));
                }
                at(&mut roots, &path).cont.push(ln.to_string());
            }
        }
    }
    Ok((base.unwrap_or(0), roots, close_indent))
}

pub fn print_step_tree(base: usize, close_indent: usize, steps: &[HtmlStep]) -> String {
    fn go(base: usize, ss: &[HtmlStep], out: &mut String) {
        for s in ss {
            out.push('\n');
            out.push_str(&" ".repeat(base + 2 * s.depth));
            out.push_str("1. ");
            if let Some(a) = &s.attrs {
                out.push('[');
                out.push_str(a);
                out.push_str("] ");
            }
            out.push_str(&s.text);
            for c in &s.cont {
                out.push('\n');
                out.push_str(c);
            }
            go(base, &s.kids, out);
        }
    }
    let mut out = String::new();
    go(base, steps, &mut out);
    out.push('\n');
    out.push_str(&" ".repeat(close_indent));
    out
}

pub fn instance_alg_text(raw: &str, param: &str, name: &str) -> String {
    let var = format!("<var>{param}</var>");
    let mut out = String::new();
    let mut i = 0;
    while i < raw.len() {
        let rest = &raw[i..];
        if let Some(r) = rest.strip_prefix("<code>") {
            if let Some(e) = r.find("</code>") {
                let inner = r[..e].replace(&var, name);
                let q = inner.len() >= 2
                    && inner.starts_with('"')
                    && inner.ends_with('"')
                    && !inner[1..inner.len() - 1].contains('"');
                if q {
                    out.push('*');
                    out.push_str(&inner);
                    out.push('*');
                } else {
                    out.push_str("<code>");
                    out.push_str(&inner);
                    out.push_str("</code>");
                }
                i += "<code>".len() + e + "</code>".len();
                continue;
            }
        }
        if let Some(r) = rest.strip_prefix("*\"") {
            if let Some(e) = r.find("\"*") {
                out.push_str("*\"");
                out.push_str(&r[..e].replace(&var, name));
                out.push_str("\"*");
                i += 2 + e + 2;
                continue;
            }
        }
        let ch = rest.chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }
    out
}

fn earliest(s: &str, from: usize, pats: &[&str]) -> Option<(usize, usize)> {
    pats.iter()
        .enumerate()
        .filter_map(|(k, p)| s[from..].find(p).map(|o| (from + o, k)))
        .min_by_key(|&(pos, _)| pos)
}

#[derive(Clone, Debug)]
pub struct SpliceItem {
    pub start: usize,
    pub end: usize,
    pub text: String,
    pub label: String,
}

impl HtmlSpec {
    pub fn scan(src: String) -> Result<Self, String> {
        let s = &src;
        let mut clauses: Vec<ClauseInfo> = Vec::new();
        let mut stack: Vec<Option<usize>> = Vec::new();
        let mut block_counts: BTreeMap<String, usize> = BTreeMap::new();
        let mut blocks = Vec::new();
        let mut algs = Vec::new();
        let mut alg_counts: BTreeMap<usize, usize> = BTreeMap::new();
        let mut last_alg_end: BTreeMap<usize, usize> = BTreeMap::new();
        let mut example_algs = 0usize;

        let mut i = 0;
        while let Some(off) = s[i..].find('<') {
            let p = i + off;
            let rest = &s[p..];
            let is = |t: &str| rest.starts_with(t) && rest[t.len()..].starts_with(|c: char| c == '>' || c == ' ');
            if is("<emu-clause") || is("<emu-annex") {
                let end = p + rest.find('>').ok_or("unclosed emu-clause/annex")? + 1;
                let tag = &s[p..end];
                let entry = attr(tag, "id").map(|id| {
                    clauses.push(ClauseInfo {
                        id,
                        start: end,
                        end: 0,
                        h1: String::new(),
                    });
                    clauses.len() - 1
                });
                stack.push(entry);
                i = end;
            } else if rest.starts_with("</emu-clause>") || rest.starts_with("</emu-annex>") {
                let c = stack.pop().ok_or_else(|| format!("spec.html:{}: unbalanced clause close", line_of(s, p)))?;
                if let Some(ci) = c {
                    clauses[ci].end = p;
                }
                i = p + 1;
            } else if is("<emu-grammar") {
                let gt = p + rest.find('>').ok_or("unclosed emu-grammar")? + 1;
                let close = gt + s[gt..].find("</emu-grammar>").ok_or("unclosed emu-grammar")?;
                let tag = &s[p..gt];
                let attrs = tag["<emu-grammar".len()..tag.len() - 1].trim();
                let is_def = attrs.contains("type=\"definition\"") && !attrs.split_whitespace().any(|w| w == "example");
                if is_def {
                    let ci = stack
                        .iter()
                        .rev()
                        .find_map(|x| *x)
                        .ok_or_else(|| format!("spec.html:{}: definition grammar outside clause", line_of(s, p)))?;
                    let cid = clauses[ci].id.clone();
                    let k = *block_counts.entry(cid.clone()).or_insert(0);
                    block_counts.insert(cid.clone(), k + 1);
                    blocks.push(HtmlBlock {
                        clause: cid,
                        clause_k: k,
                        span: (gt, close),
                        line: line_of(s, p),
                        text: s[gt..close].to_string(),
                    });
                }
                i = close + "</emu-grammar>".len();
            } else if is("<emu-alg") {
                let gt = p + rest.find('>').ok_or("unclosed emu-alg")? + 1;
                let close = gt + s[gt..].find("</emu-alg>").ok_or("unclosed emu-alg")?;
                let end_tag = close + "</emu-alg>".len();
                let ci = stack
                    .iter()
                    .rev()
                    .find_map(|x| *x)
                    .ok_or_else(|| format!("spec.html:{}: emu-alg outside clause", line_of(s, p)))?;
                let attrs = s[p + "<emu-alg".len()..gt - 1].trim().to_string();
                let idx = *alg_counts.entry(ci).or_insert(0);
                alg_counts.insert(ci, idx + 1);
                let lo = last_alg_end.get(&ci).copied().unwrap_or(clauses[ci].start);
                last_alg_end.insert(ci, end_tag);
                if attrs.split_whitespace().any(|w| w == "example") {
                    example_algs += 1;
                } else {
                    let raw = s[gt..close].to_string();
                    let (base, steps, close_indent) =
                        step_tree(&raw).map_err(|e| format!("spec.html:{}: {e}", line_of(s, p)))?;
                    let (key_span, key_text) = if let Some(rel_g) = s[lo..p].rfind("<emu-grammar") {
                        let abs_g = lo + rel_g;
                        let a = abs_g + s[abs_g..].find('>').unwrap() + 1;
                        let b = a + s[a..].find("</emu-grammar>").unwrap();
                        (Some((a, b)), Some(s[a..b].to_string()))
                    } else {
                        (None, None)
                    };
                    algs.push(HtmlAlg {
                        clause: clauses[ci].id.clone(),
                        idx,
                        span: (gt, close),
                        line: line_of(s, p),
                        attrs,
                        text: raw,
                        key_span,
                        key_text,
                        base,
                        close_indent,
                        steps,
                    });
                }
                i = end_tag;
            } else {
                i = p + 1;
            }
        }
        if !stack.is_empty() {
            return Err("unclosed clause at end of spec.html".into());
        }
        for c in &mut clauses {
            let body = &s[c.start..c.end];
            let t = body.trim_start();
            if let Some(r) = t.strip_prefix("<h1>") {
                if let Some(e) = r.find("</h1>") {
                    c.h1 = r[..e].to_string();
                }
            }
        }

        // Equation bullets: `<li>\n  The <SDO> of <emu-grammar>...</emu-grammar> is ...\n</li>`
        let mut eqs = Vec::new();
        let mut scan_pos = 0;
        while let Some(rel) = s[scan_pos..].find("<li>") {
            let li_pos = scan_pos + rel;
            let body_start = li_pos + 4;
            let Some(rel_end) = s[body_start..].find("</li>") else {
                scan_pos = body_start;
                continue;
            };
            let body_end = body_start + rel_end;
            scan_pos = body_end + 5;
            let raw = &s[body_start..body_end];
            let t = raw.trim_start();
            let Some(after_the) = t.strip_prefix("The ") else { continue };
            let Some(sp) = after_the.find(' ') else { continue };
            if sp == 0 || !after_the[..sp].chars().all(|c| c.is_ascii_alphanumeric()) {
                continue;
            }
            if !after_the[sp..].starts_with(" of <emu-grammar") {
                continue;
            }
            let indent = column(s, li_pos);
            let lead = format!("\n{}", " ".repeat(indent + 2));
            let trail = format!("\n{}", " ".repeat(indent));
            let Some(line_text) = raw
                .strip_prefix(&lead)
                .and_then(|r| r.strip_suffix(&trail))
                .filter(|x| !x.contains('\n'))
            else {
                return Err(format!("spec.html:{}: equation bullet not formatted on one line", line_of(s, li_pos)));
            };
            let ci = clauses
                .iter()
                .enumerate()
                .filter(|(_, c)| c.start <= li_pos && li_pos < c.end)
                .max_by_key(|(_, c)| c.start)
                .map(|(idx, _)| idx)
                .ok_or_else(|| format!("spec.html:{}: equation outside clause", line_of(s, li_pos)))?;
            let idx = *alg_counts.entry(ci).or_insert(0);
            alg_counts.insert(ci, idx + 1);
            eqs.push(HtmlEq {
                clause: clauses[ci].id.clone(),
                idx,
                span: (body_start, body_end),
                line: line_of(s, li_pos),
                indent,
                text: raw.to_string(),
                line_text: line_text.to_string(),
            });
        }

        // Early error rules inside `<h1>Static Semantics: Early Errors</h1>` clauses
        let mut early = Vec::new();
        for (ci, c) in clauses.iter().enumerate() {
            if c.h1 != "Static Semantics: Early Errors" {
                continue;
            }
            let body = &s[c.start..c.end];
            let Some(h1_rel) = body.find("<h1>Static Semantics: Early Errors</h1>") else {
                continue;
            };
            let abs_h1 = c.start + h1_rel;
            let line_start = s[..abs_h1].rfind('\n').map_or(0, |k| k + 1);
            let col = abs_h1 - line_start;
            let end = ["<emu-clause", "<emu-annex", "</emu-clause>", "</emu-annex>"]
                .iter()
                .filter_map(|t| s[abs_h1..].find(t).map(|o| abs_h1 + o))
                .min()
                .unwrap_or(c.end)
                .min(c.end + "</emu-clause>".len());
            let mut idx = *alg_counts.entry(ci).or_insert(0);
            let mut last = abs_h1 + "<h1>Static Semantics: Early Errors</h1>".len();
            let ul_needle = format!("{}<ul>", " ".repeat(col));
            let mut cur = last;
            while cur < end {
                let ls = cur;
                let nl = s[ls..end].find('\n').map_or(end, |o| ls + o);
                cur = if nl < end { nl + 1 } else { end };
                let line_slice = &s[ls..nl];
                if !line_slice.starts_with(&ul_needle) {
                    continue;
                }
                let at = ls + ul_needle.len();
                let mut keys = Vec::new();
                let mut gpos = last;
                while let Some(rel_g) = s[gpos..at].find("<emu-grammar>") {
                    let a = gpos + rel_g + "<emu-grammar>".len();
                    let Some(rel_b) = s[a..at].find("</emu-grammar>") else { break };
                    let b = a + rel_b;
                    keys.push(((a, b), s[a..b].to_string()));
                    gpos = b + "</emu-grammar>".len();
                }
                let mut depth = 0usize;
                let mut li_open: Option<(usize, usize)> = None;
                let mut q = at;
                loop {
                    let Some((o, k)) = earliest(s, q, &["<li>", "</li>", "<ul", "</ul>"]) else {
                        return Err(format!("spec.html:{}: unclosed <ul> in Early Errors", line_of(s, ls)));
                    };
                    if o >= end {
                        break;
                    }
                    match (k, depth) {
                        (0, 0) => {
                            li_open = Some((column(s, o), o + 4));
                            q = o + 4;
                        }
                        (1, 0) => {
                            let (indent, a) = li_open.take().ok_or("stray </li> in Early Errors")?;
                            let raw = &s[a..o];
                            let lead = format!("\n{}", " ".repeat(indent + 2));
                            let trail = format!("\n{}", " ".repeat(indent));
                            let (layout, body_text) = if !raw.contains('\n') {
                                (EarlyLayout::Inline, raw.to_string())
                            } else if raw
                                .strip_prefix(&lead)
                                .and_then(|r| r.strip_suffix(&trail))
                                .is_some_and(|x| !x.contains('\n'))
                            {
                                let inner = raw
                                    .strip_prefix(&lead)
                                    .unwrap()
                                    .strip_suffix(&trail)
                                    .unwrap()
                                    .to_string();
                                (EarlyLayout::Block, inner)
                            } else {
                                (EarlyLayout::Raw, raw.to_string())
                            };
                            early.push(HtmlEarly {
                                clause: c.id.clone(),
                                idx,
                                span: (a, o),
                                line: line_of(s, a),
                                indent,
                                layout,
                                text: raw.to_string(),
                                body_text,
                                keys: keys.clone(),
                            });
                            idx += 1;
                            q = o + 5;
                        }
                        (2, _) => {
                            depth += 1;
                            q = o + 3;
                        }
                        (3, 0) => {
                            last = o + 5;
                            cur = last;
                            break;
                        }
                        (3, _) => {
                            depth -= 1;
                            q = o + 5;
                        }
                        _ => q = o + 1,
                    }
                }
            }
            alg_counts.insert(ci, idx);
        }

        let mut alg_map = BTreeMap::new();
        for (k, a) in algs.iter().enumerate() {
            alg_map.insert((a.clause.clone(), a.idx), k);
        }
        let mut eq_map = BTreeMap::new();
        for (k, eq) in eqs.iter().enumerate() {
            eq_map.insert((eq.clause.clone(), eq.idx), k);
        }
        let mut early_map = BTreeMap::new();
        for (k, e) in early.iter().enumerate() {
            early_map.insert((e.clause.clone(), e.idx), k);
        }

        Ok(HtmlSpec {
            src,
            clauses,
            blocks,
            algs,
            alg_map,
            eqs,
            eq_map,
            early,
            early_map,
            example_algs,
        })
    }

    pub fn instance(&self, cid: &str, idx: usize) -> Option<String> {
        let (tmpl, name) = cid.split_once('/')?;
        if !self.src.contains(&format!("<dfn>%{name}%</dfn>")) {
            return None;
        }
        let c = self.clauses.iter().find(|c| c.id == tmpl)?;
        // Find `_Param_` in c.h1
        let mut param = None;
        let mut rest = c.h1.as_str();
        while let Some(i) = rest.find('_') {
            let after = &rest[i + 1..];
            if let Some(j) = after.find('_') {
                let w = &after[..j];
                if !w.is_empty() && w.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '_') {
                    param = Some(w.to_string());
                    break;
                }
                rest = &after[j + 1..];
            } else {
                break;
            }
        }
        let param = param?;
        let ai = self.alg_map.get(&(tmpl.to_string(), idx)).copied()?;
        Some(instance_alg_text(&self.algs[ai].text, &param, name))
    }

    pub fn block_by_clause_k(&self, clause: &str, k: usize) -> Option<&HtmlBlock> {
        self.blocks.iter().find(|b| b.clause == clause && b.clause_k == k)
    }

    pub fn splice(&self, mut items: Vec<SpliceItem>) -> Result<String, String> {
        items.sort_by(|a, b| a.start.cmp(&b.start).then_with(|| b.end.cmp(&a.end)));
        let mut dedup: Vec<SpliceItem> = Vec::with_capacity(items.len());
        for it in items {
            if let Some(prev) = dedup.last() {
                if prev.start == it.start && prev.end == it.end {
                    if prev.text != it.text {
                        return Err(format!(
                            "conflicting splice replacements at {}..{} ({} vs {})",
                            it.start, it.end, prev.label, it.label
                        ));
                    }
                    continue;
                }
                if it.start < prev.end {
                    if it.end <= prev.end {
                        // Nested span: must match slice inside outer replacement byte-for-byte.
                        let off_a = it.start - prev.start;
                        let off_b = it.end - prev.start;
                        if prev.text.get(off_a..off_b) != Some(it.text.as_str()) {
                            return Err(format!(
                                "nested splice mismatch: {} ({}..{}) inside {} ({}..{})",
                                it.label, it.start, it.end, prev.label, prev.start, prev.end
                            ));
                        }
                        continue;
                    }
                    return Err(format!(
                        "overlapping splice spans: {} ({}..{}) and {} ({}..{})",
                        prev.label, prev.start, prev.end, it.label, it.start, it.end
                    ));
                }
            }
            dedup.push(it);
        }
        let mut out = String::with_capacity(self.src.len());
        let mut pos = 0usize;
        let mut seen_labels = BTreeSet::new();
        for it in dedup {
            let _ = seen_labels.insert(it.label);
            out.push_str(&self.src[pos..it.start]);
            out.push_str(&it.text);
            pos = it.end;
        }
        out.push_str(&self.src[pos..]);
        Ok(out)
    }
}
