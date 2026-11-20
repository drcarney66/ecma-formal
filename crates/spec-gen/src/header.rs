//! Clause headers: the `<h1>` signature (name, parameters with their type
//! phrases, return type) and `dl.header`'s `for:` receiver.

use crate::spec::Clause;

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    /// the type phrase of a structured header
    pub ty: Option<String>,
    pub optional: bool,
    pub rest: bool,
}

#[derive(Clone, Debug, Default)]
pub struct Header {
    pub params: Vec<Param>,
    pub ret: Option<String>,
    /// the receiver variable and its type phrase
    pub recv: Option<(String, String)>,
}

/// `_name_` at the start of `s` (after `...` for a rest parameter).
fn var_at(s: &str) -> Option<(String, &str)> {
    let r = s.strip_prefix('_')?;
    let e = r.find('_')?;
    let name = &r[..e];
    if name.is_empty() || !name.chars().all(|c| c.is_ascii_alphanumeric()) {
        return None;
    }
    Some((name.to_string(), &r[e + 1..]))
}

/// Split a structured parameter list at the commas before `[optional] _x_:`.
fn split_params(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut start = 0;
    let b = s.as_bytes();
    for i in 0..b.len() {
        if b[i] == b',' {
            let rest = s[i + 1..].trim_start();
            let rest = rest.strip_prefix("optional ").unwrap_or(rest);
            if let Some((_, after)) = var_at(rest) {
                if after.trim_start().starts_with(':') {
                    out.push(&s[start..i]);
                    start = i + 1;
                }
            }
        }
    }
    out.push(&s[start..]);
    out
}

/// The `)` matching the `(` at `open`.
fn matching(s: &str, open: usize) -> Option<usize> {
    let mut depth = 0;
    for (i, c) in s[open..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(open + i);
                }
            }
            _ => {}
        }
    }
    None
}

/// A built-in function's parameter named in its clause's prose before the steps ("… is a
/// built-in function that takes an argument _x_."), where the `<h1>` lists none.
pub fn prose_params(prose: &str) -> Vec<Param> {
    let prose = prose.split("<emu-alg").next().unwrap_or("");
    let Some(at) = prose.find("built-in function that takes an argument ") else { return vec![] };
    var_at(&prose[at + "built-in function that takes an argument ".len()..])
        .map(|(name, _)| vec![Param { name, ty: None, optional: false, rest: false }])
        .unwrap_or_default()
}

/// An Annex B row's parameters: those of the SDO that the last "semantics of X [with argument(s) _a_ …]"
/// paragraph of `lead` (the clause's text before the row) extends, whose names the paragraph must repeat.
pub fn extended_params(lead: &str, clauses: &[Clause]) -> Result<Vec<Param>, String> {
    let Some(p) = lead.split("<p>").filter(|p| p.contains("semantics of ")).last() else { return Ok(vec![]) };
    let p = p.split("</p>").next().unwrap_or(p);
    let rest = &p[p.find("semantics of ").unwrap() + "semantics of ".len()..];
    let name: String = rest.chars().take_while(|c| c.is_ascii_alphanumeric()).collect();
    let Some(c) = clauses.iter().find(|c| !name.is_empty() && c.ty.as_deref() == Some("sdo") && c.op().as_deref() == Some(name.as_str())) else { return Ok(vec![]) };
    let params = parse(c).params;
    let said: Vec<String> = rest.split('_').skip(1).step_by(2).map(String::from).collect();
    if said != params.iter().map(|q| q.name.clone()).collect::<Vec<_>>() {
        return Err(format!("{name}'s extension names {said:?}, its parameters differ"));
    }
    Ok(params)
}

pub fn parse(c: &Clause) -> Header {
    let mut h = Header::default();
    let text = c.h1_text();
    if let Some(open) = text.find('(') {
        let close = matching(&text, open).unwrap_or(text.len());
        if close > open {
            let params = &text[open + 1..close];
            let after = text[close + 1..].trim();
            let structured = c.ty.is_some() && (params.contains(':') || after.starts_with(':'));
            if structured {
                for part in split_params(params) {
                    let t = part.trim().trim_end_matches(',').trim();
                    if t.is_empty() {
                        continue;
                    }
                    let (optional, t) = match t.strip_prefix("optional ") {
                        Some(r) => (true, r),
                        None => (false, t),
                    };
                    if let Some((name, rest)) = var_at(t) {
                        let ty = rest.trim_start().strip_prefix(':').map(|x| x.trim().to_string());
                        h.params.push(Param { name, ty, optional, rest: false });
                    }
                }
                if let Some(r) = after.strip_prefix(':') {
                    h.ret = Some(r.trim().to_string());
                }
            } else if c.ty.is_some() || params.contains('_') {
                let mut depth_opt = false;
                let mut i = 0;
                let p = params.as_bytes();
                while i < p.len() {
                    match p[i] {
                        b'[' => depth_opt = true,
                        b'_' => {
                            let rest = params[..i].ends_with("...");
                            if let Some((name, tail)) = var_at(&params[i..]) {
                                i = params.len() - tail.len();
                                h.params.push(Param { name, ty: None, optional: depth_opt, rest });
                                continue;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
            }
        }
    }
    if let Some(f) = c.dl_entry("for") {
        let t = crate::text::squash(&crate::text::strip_tags(&f));
        if let Some(i) = t.rfind(" _") {
            if let Some((name, rest)) = var_at(&t[i + 1..]) {
                let rest = rest.trim_start();
                if rest.is_empty() || (rest.starts_with('(') && rest.ends_with(')')) {
                    h.recv = Some((name, t[..i].to_string()));
                }
            }
        }
    }
    h
}
