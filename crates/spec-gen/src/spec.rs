//! spec.html, scanned by hand: the clause tree (ids, section numbers, types,
//! headers) and every `<emu-alg>` with its clause, production and step tree.

#[derive(Clone, Debug, Default)]
pub struct Clause {
    pub id: String,
    pub number: String,
    pub ty: Option<String>,
    pub aoid: Option<String>,
    /// offset just after the opening tag, and of the closing tag
    pub start: usize,
    pub end: usize,
    /// the raw `<h1>` content
    pub h1: String,
    /// the raw `<dl class="header">` content (before the first algorithm or subclause)
    pub dl: String,
    /// the instance this clause was expanded for
    pub inst: Option<Inst>,
    /// the ids it had before (`oldids`)
    pub oldids: Vec<String>,
}

impl Clause {
    /// The `<h1>` text: tags removed, entities decoded, white space squashed.
    pub fn h1_text(&self) -> String {
        crate::text::squash(&crate::text::unescape(&crate::text::strip_tags(&self.h1)).replace('`', ""))
    }

    /// The name before any parameter list.
    pub fn title(&self) -> String {
        let t = self.h1_text();
        match t.find(" (") {
            Some(i) if self.ty.is_some() || t[i..].contains('_') || t[i..].starts_with(" ( )") => t[..i].to_string(),
            _ => t,
        }
    }

    /// The operation this clause defines: its `aoid`, or a typed clause's title
    /// without "Static Semantics:" / "Runtime Semantics:".
    pub fn op(&self) -> Option<String> {
        if let Some(a) = &self.aoid {
            return Some(a.clone());
        }
        self.ty.as_ref()?;
        let t = self.title();
        let t = t.strip_prefix("Static Semantics: ").or_else(|| t.strip_prefix("Runtime Semantics: ")).unwrap_or(&t);
        Some(t.to_string())
    }

    /// The `dl.header` entry `name`, raw.
    pub fn dl_entry(&self, name: &str) -> Option<String> {
        let key = format!("<dt>{name}</dt>");
        let i = self.dl.find(&key)? + key.len();
        let rest = &self.dl[i..];
        let a = rest.find("<dd>")? + 4;
        let b = rest[a..].find("</dd>")? + a;
        Some(rest[a..b].to_string())
    }
}

/// A step line of an algorithm.
#[derive(Clone, Debug)]
pub struct Step {
    pub depth: usize,
    /// `[id="…"]`-style attributes as written, without brackets
    pub attrs: Option<String>,
    pub text: String,
    /// continuation lines, verbatim (bullet lists, tables)
    pub cont: Vec<String>,
    pub kids: Vec<Step>,
}

#[derive(Clone, Debug)]
pub struct Alg {
    /// offset of `<emu-alg`
    pub pos: usize,
    pub line: usize,
    pub attrs: String,
    /// the text between the tags
    pub raw: String,
    pub clause: Option<usize>,
    /// index among the clause's own algorithms
    pub idx: usize,
    /// the `<emu-grammar>` this algorithm follows in its clause (an SDO row's productions), raw
    pub prod: Option<String>,
    /// the indentation of the steps at depth 0
    pub base: usize,
    pub steps: Vec<Step>,
    /// the column of `</emu-alg>`
    pub close_indent: usize,
    /// a parameterized clause's algorithm, read only through its instances
    pub tmpl: bool,
}

impl Alg {
    pub fn example(&self) -> bool {
        self.attrs.contains("example")
    }
}

/// An equation SDO bullet: `<li>The SV of <emu-grammar>…</emu-grammar> is ….</li>`.
#[derive(Clone, Debug)]
pub struct Eq {
    pub line: usize,
    pub clause: usize,
    /// its position after its clause's emu-algs, among them and the clause's equations
    pub idx: usize,
    /// the column of `<li>`
    pub indent: usize,
    /// the content between the tags
    pub raw: String,
    /// the sentence
    pub text: String,
}

pub struct Spec {
    pub clauses: Vec<Clause>,
    pub algs: Vec<Alg>,
    pub eqs: Vec<Eq>,
    pub early: crate::early::Early,
}

pub fn line_of(s: &str, pos: usize) -> usize {
    s[..pos].bytes().filter(|&b| b == b'\n').count() + 1
}

pub fn attr(tag: &str, name: &str) -> Option<String> {
    let key = format!(" {name}=\"");
    let i = tag.find(&key)? + key.len();
    let j = tag[i..].find('"')? + i;
    Some(tag[i..j].to_string())
}

fn roman_letter(n: usize) -> String {
    char::from(b'A' + (n - 1) as u8).to_string()
}

pub fn scan(html: &str) -> Result<Spec, String> {
    let s = html;
    let mut clauses: Vec<Clause> = Vec::new();
    // open clause tags: Some(index) for clauses with ids
    let mut stack: Vec<Option<usize>> = Vec::new();
    let mut counters: Vec<usize> = vec![0];
    let mut labels: Vec<String> = Vec::new();
    let (mut top_clause, mut top_annex) = (0, 0);
    let mut algs = Vec::new();
    let mut i = 0;
    while let Some(off) = s[i..].find('<') {
        let p = i + off;
        let rest = &s[p..];
        let is = |t: &str| rest.starts_with(t) && rest[t.len()..].starts_with(|c: char| c == '>' || c == ' ');
        if is("<emu-clause") || is("<emu-annex") {
            let end = p + rest.find('>').ok_or("unclosed tag")? + 1;
            let tag = &s[p..end];
            let label = if stack.is_empty() {
                if tag.starts_with("<emu-clause") {
                    top_clause += 1;
                    top_clause.to_string()
                } else {
                    top_annex += 1;
                    roman_letter(top_annex)
                }
            } else {
                *counters.last_mut().unwrap() += 1;
                format!("{}.{}", labels.last().unwrap(), counters.last().unwrap())
            };
            labels.push(label.clone());
            counters.push(0);
            let entry = attr(tag, "id").map(|id| {
                clauses.push(Clause {
                    id,
                    number: label,
                    ty: attr(tag, "type"),
                    aoid: attr(tag, "aoid"),
                    start: end,
                    end: 0,
                    oldids: attr(tag, "oldids").map(|x| x.split(',').map(|x| x.trim().to_string()).filter(|x| !x.is_empty()).collect()).unwrap_or_default(),
                    ..Default::default()
                });
                clauses.len() - 1
            });
            stack.push(entry);
            i = end;
        } else if rest.starts_with("</emu-clause>") || rest.starts_with("</emu-annex>") {
            let c = stack.pop().ok_or_else(|| format!("spec.html:{}: unbalanced close", line_of(s, p)))?;
            counters.pop();
            labels.pop();
            if let Some(c) = c {
                clauses[c].end = p;
            }
            i = p + 1;
        } else if is("<emu-alg") {
            let gt = p + rest.find('>').ok_or("unclosed emu-alg")? + 1;
            let close = gt + s[gt..].find("</emu-alg>").ok_or("unclosed emu-alg")?;
            let clause = stack.iter().rev().find_map(|x| *x);
            let raw = s[gt..close].to_string();
            let (base, steps, close_indent) = step_tree(&raw).map_err(|e| format!("spec.html:{}: {e}", line_of(s, p)))?;
            let prod = clause.and_then(|c| {
                let seg = &s[clauses[c].start..p];
                let lg = seg.rfind("<emu-grammar")?;
                if seg.rfind("</emu-alg>").is_some_and(|la| la > lg) {
                    return None;
                }
                let g = &seg[lg..];
                let a = g.find('>')? + 1;
                let b = g.find("</emu-grammar>")?;
                Some(g[a..b].to_string())
            });
            algs.push(Alg {
                prod,
                pos: p,
                line: line_of(s, p),
                attrs: s[p + "<emu-alg".len()..gt - 1].trim().to_string(),
                raw,
                clause,
                idx: 0,
                base,
                steps,
                close_indent,
                tmpl: false,
            });
            i = close + "</emu-alg>".len();
        } else {
            i = p + 1;
        }
    }
    if !stack.is_empty() {
        return Err("unclosed clause at end of file".into());
    }
    let mut count = vec![0usize; clauses.len()];
    for a in &mut algs {
        if let Some(c) = a.clause {
            a.idx = count[c];
            count[c] += 1;
        }
    }
    for c in &mut clauses {
        let body = &s[c.start..c.end];
        let t = body.trim_start();
        if let Some(r) = t.strip_prefix("<h1>") {
            if let Some(e) = r.find("</h1>") {
                c.h1 = r[..e].to_string();
            }
        }
        let stop = ["<emu-alg", "<emu-clause", "<emu-annex"].iter().filter_map(|x| body.find(x)).min().unwrap_or(body.len());
        if let Some(a) = body[..stop].find("<dl class=\"header\">") {
            let a = a + "<dl class=\"header\">".len();
            if let Some(b) = body[a..stop].find("</dl>") {
                c.dl = body[a..a + b].to_string();
            }
        }
    }
    let eqs = equations(s, &clauses, &count)?;
    for e in &eqs {
        count[e.clause] += 1;
    }
    let early = crate::early::scan(s, &clauses, &count)?;
    instantiate(s, &mut clauses, &mut algs)?;
    Ok(Spec { clauses, algs, eqs, early })
}

/// The instance a clause was expanded for: its parameterized clause, the parameter and the name.
#[derive(Clone, Debug, Default)]
pub struct Inst {
    pub of: usize,
    pub param: String,
    pub name: String,
}

impl Spec {
    /// The clause a clause was expanded from (itself if it is not an instance).
    pub fn home(&self, c: usize) -> usize {
        self.clauses[c].inst.as_ref().map_or(c, |i| i.of)
    }
}

/// The element (clause or emu-table) with the id, as a span of the text.
fn element_span(s: &str, clauses: &[Clause], id: &str) -> Option<std::ops::Range<usize>> {
    if let Some(c) = clauses.iter().find(|c| c.id == id) {
        return Some(c.start..c.end);
    }
    let a = s.find(&format!("<emu-table id=\"{id}\""))?;
    Some(a..a + s[a..].find("</emu-table>")?)
}

/// Each clause parameter with its instances: a sentence "references to _P_ … should be replaced
/// with the appropriate … name from X" (X a clause or table, or "the above table"), and the
/// `<dfn>%Name%</dfn>` definitions in X, in document order.
pub fn parameters(s: &str, clauses: &[Clause]) -> Vec<(String, Vec<String>)> {
    let mut out: Vec<(String, Vec<String>)> = Vec::new();
    for (at, _) in s.match_indices("references to _") {
        let rest = &s[at + "references to _".len()..];
        let Some(e) = rest.find('_') else { continue };
        let param = &rest[..e];
        let sent = &rest[..rest.find("</p>").unwrap_or(rest.len())];
        if !param.chars().all(|c| c.is_ascii_alphanumeric()) || !sent.contains("should be replaced with the appropriate") {
            continue;
        }
        let span = if let Some(x) = sent.find("href=\"#") {
            let id = sent[x + "href=\"#".len()..].split('"').next().unwrap_or("");
            element_span(s, clauses, id)
        } else if sent.contains("the above table") {
            s[..at].rfind("<emu-table id=\"").and_then(|a| Some(a..a + s[a..].find("</emu-table>")?))
        } else {
            None
        };
        let Some(span) = span else { continue };
        let mut names: Vec<String> = Vec::new();
        for (d, _) in s[span.clone()].match_indices("<dfn>%") {
            let r = &s[span.start + d + "<dfn>%".len()..];
            if let Some(n) = r.find("%</dfn>").map(|k| &r[..k]) {
                if n.chars().all(|c| c.is_ascii_alphanumeric()) && !names.iter().any(|x| x == n) {
                    names.push(n.to_string());
                }
            }
        }
        if !names.is_empty() && !out.iter().any(|(p, _)| p == param) {
            out.push((param.to_string(), names));
        }
    }
    out
}

/// An instance's algorithm text: `<var>P</var>` replaced by the name inside code (`<code>…</code>`)
/// and String (`*"…"*`) forms; a code form that is one quoted String is written as the String `*"…"*`.
pub fn instance_alg_text(raw: &str, param: &str, name: &str) -> String {
    let var = format!("<var>{param}</var>");
    let mut out = String::new();
    let mut i = 0;
    while i < raw.len() {
        let rest = &raw[i..];
        if let Some(r) = rest.strip_prefix("<code>") {
            if let Some(e) = r.find("</code>") {
                let inner = r[..e].replace(&var, name);
                let q = inner.len() >= 2 && inner.starts_with('"') && inner.ends_with('"') && inner[1..inner.len() - 1].find('"').is_none();
                if q {
                    out.push_str(&format!("*{inner}*"));
                } else {
                    out.push_str(&format!("<code>{inner}</code>"));
                }
                i += "<code>".len() + e + "</code>".len();
                continue;
            }
        }
        if let Some(r) = rest.strip_prefix("*\"") {
            if let Some(e) = r.find("\"*") {
                out.push_str(&format!("*\"{}\"*", r[..e].replace(&var, name)));
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

impl Clause {
    /// The clause's text: for an instance, the parameterized clause's with every `_P_` and
    /// `<var>P</var>` replaced by the instance's name.
    pub fn body(&self, s: &str) -> String {
        let b = &s[self.start..self.end];
        match &self.inst {
            Some(i) => b.replace(&format!("_{}_", i.param), &i.name).replace(&format!("<var>{}</var>", i.param), &i.name),
            None => b.to_string(),
        }
    }
}

/// Each clause whose heading names a parameter, expanded per instance (appended, instance by
/// instance in document order): heading and op name substituted, algorithms by `instance_alg_text`.
/// The parameterized algorithms are kept as templates.
fn instantiate(s: &str, clauses: &mut Vec<Clause>, algs: &mut Vec<Alg>) -> Result<(), String> {
    for (param, names) in parameters(s, clauses) {
        let hole = format!("_{param}_");
        let tmpl: Vec<usize> = (0..clauses.len()).filter(|&c| clauses[c].inst.is_none() && clauses[c].h1.contains(&hole)).collect();
        for &c in &tmpl {
            for a in algs.iter_mut().filter(|a| a.clause == Some(c)) {
                a.tmpl = true;
            }
        }
        for n in &names {
            for &c in &tmpl {
                let t = &clauses[c];
                let mut k = Clause { id: format!("{}/{n}", t.id), h1: t.h1.replace(&hole, n), inst: Some(Inst { of: c, param: param.clone(), name: n.clone() }), ..t.clone() };
                k.aoid = t.aoid.as_ref().map(|x| x.replace(&hole, n));
                k.oldids = t.oldids.iter().map(|o| format!("{o}/{n}")).collect();
                clauses.push(k);
                let ki = clauses.len() - 1;
                let mine: Vec<Alg> = algs.iter().filter(|a| a.clause == Some(c)).cloned().collect();
                for a in mine {
                    let raw = instance_alg_text(&a.raw, &param, n);
                    let (base, steps, close_indent) = step_tree(&raw).map_err(|e| format!("spec.html:{}: {e}", a.line))?;
                    algs.push(Alg { raw, base, steps, close_indent, clause: Some(ki), tmpl: false, ..a });
                }
            }
        }
    }
    Ok(())
}

/// A step line: indent, marker digits, attributes and text.
pub fn step_line(ln: &str) -> Option<(usize, Option<String>, String)> {
    let indent = ln.len() - ln.trim_start().len();
    let t = &ln[indent..];
    let rest = t.strip_prefix("1. ")?;
    if let Some(r) = rest.strip_prefix('[') {
        let e = r.find(']')?;
        let after = &r[e + 1..];
        let text = after.strip_prefix(' ').unwrap_or(after);
        return Some((indent, Some(r[..e].to_string()), text.to_string()));
    }
    Some((indent, None, rest.to_string()))
}

/// The step tree of an algorithm body, its base indentation and the column of
/// the closing tag. Layout must be regular: `1. ` markers, two spaces a level.
pub fn step_tree(body: &str) -> Result<(usize, Vec<Step>, usize), String> {
    let lines: Vec<&str> = body.split('\n').collect();
    if lines.len() < 2 || !lines[0].is_empty() {
        return Err("an emu-alg body that does not start on a new line".into());
    }
    let last = lines[lines.len() - 1];
    if !last.chars().all(|c| c == ' ') {
        return Err("text before </emu-alg> on its line".into());
    }
    let close_indent = last.len();
    let mut roots: Vec<Step> = Vec::new();
    let mut base = None;
    // path of open steps (indices into the tree)
    let mut path: Vec<usize> = Vec::new();
    fn at<'a>(roots: &'a mut Vec<Step>, path: &[usize]) -> &'a mut Step {
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
                let st = Step { depth, attrs, text, cont: Vec::new(), kids: Vec::new() };
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

/// A step line printed from its depth.
pub fn print_step_line(base: usize, s: &Step, text: &str) -> String {
    let mut out = " ".repeat(base + 2 * s.depth);
    out.push_str("1. ");
    if let Some(a) = &s.attrs {
        out.push('[');
        out.push_str(a);
        out.push_str("] ");
    }
    out.push_str(text);
    out
}

/// An algorithm body printed from its steps, each step's text from `text`.
pub fn print_body(a: &Alg, text: &mut dyn FnMut(&Step) -> String) -> String {
    fn go(base: usize, ss: &[Step], out: &mut String, text: &mut dyn FnMut(&Step) -> String) {
        for s in ss {
            out.push('\n');
            out.push_str(&print_step_line(base, s, &text(s)));
            for c in &s.cont {
                out.push('\n');
                out.push_str(c);
            }
            go(base, &s.kids, out, text);
        }
    }
    let mut out = String::new();
    go(a.base, &a.steps, &mut out, text);
    out.push('\n');
    out.push_str(&" ".repeat(a.close_indent));
    out
}

/// Every step of a tree with its label path (`1.a.ii`).
pub fn labelled(ss: &[Step]) -> Vec<(String, &Step)> {
    fn label(depth: usize, n: usize) -> String {
        match depth % 3 {
            0 => n.to_string(),
            1 => {
                let mut s = String::new();
                let mut n = n;
                while n > 0 {
                    let r = (n - 1) % 26;
                    s.insert(0, char::from(b'a' + r as u8));
                    n = (n - 1) / 26;
                }
                s
            }
            _ => crate::text::roman(n),
        }
    }
    fn go<'a>(ss: &'a [Step], prefix: &str, out: &mut Vec<(String, &'a Step)>) {
        for (k, s) in ss.iter().enumerate() {
            let l = label(s.depth, k + 1);
            let p = if prefix.is_empty() { l } else { format!("{prefix}.{l}") };
            out.push((p.clone(), s));
            go(&s.kids, &p, out);
        }
    }
    let mut out = Vec::new();
    go(ss, "", &mut out);
    out
}

/// The innermost clause around `pos`.
fn clause_at(clauses: &[Clause], pos: usize) -> Option<usize> {
    clauses.iter().enumerate().filter(|(_, c)| c.inst.is_none() && c.start <= pos && pos < c.end).max_by_key(|(_, c)| c.start).map(|(i, _)| i)
}

/// The equation bullets, each `<li>` then the sentence on its own line, two
/// columns in, then `</li>` at the `<li>`'s column.
fn equations(s: &str, clauses: &[Clause], algs_per_clause: &[usize]) -> Result<Vec<Eq>, String> {
    let mut out = Vec::new();
    let mut per: Vec<usize> = algs_per_clause.to_vec();
    for (i, _) in s.match_indices("<li>") {
        let a = i + 4;
        let Some(e) = s[a..].find("</li>").map(|e| a + e) else { continue };
        let raw = &s[a..e];
        let t = raw.trim_start();
        let Some(rest) = t.strip_prefix("The ") else { continue };
        let Some(sp) = rest.find(' ') else { continue };
        if !rest[sp..].starts_with(" of <emu-grammar") || !rest[..sp].chars().all(|c| c.is_ascii_alphanumeric()) {
            continue;
        }
        let line_start = s[..i].rfind('\n').map(|x| x + 1).unwrap_or(0);
        let indent = i - line_start;
        let lead = format!("\n{}", " ".repeat(indent + 2));
        let trail = format!("\n{}", " ".repeat(indent));
        let text = raw
            .strip_prefix(&lead)
            .and_then(|r| r.strip_suffix(&trail))
            .filter(|t| !t.contains('\n'))
            .ok_or_else(|| format!("spec.html:{}: an equation bullet not on one line two columns in", line_of(s, i)))?;
        let clause = clause_at(clauses, i).ok_or_else(|| format!("spec.html:{}: an equation outside a clause", line_of(s, i)))?;
        out.push(Eq { line: line_of(s, i), clause, idx: per[clause], indent, raw: raw.to_string(), text: text.to_string() });
        per[clause] += 1;
    }
    Ok(out)
}
