//! Sidecar name-keyed metadata tables under `spec/html/`.

use spectec::ast::GrammarId;
use spectec::print::esc_str;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::Path;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ItemKey {
    pub clause: String,
    pub idx: usize,
}

impl ItemKey {
    pub fn new(clause: impl Into<String>, idx: usize) -> Self {
        Self { clause: clause.into(), idx }
    }
    pub fn fmt_ref(&self) -> String {
        if self.idx == 0 {
            format!("@{}", self.clause)
        } else {
            format!("@{}#{}", self.clause, self.idx)
        }
    }
    pub fn parse_ref(s: &str) -> Result<Self, String> {
        let rest = s.strip_prefix('@').ok_or_else(|| format!("expected `@clause` ref, got {s:?}"))?;
        if let Some((c, i)) = rest.rsplit_once('#') {
            let idx = i.parse::<usize>().map_err(|e| format!("bad index in {s:?}: {e}"))?;
            Ok(Self { clause: c.to_string(), idx })
        } else {
            Ok(Self { clause: rest.to_string(), idx: 0 })
        }
    }
}

pub fn unesc_str(raw: &str) -> Result<String, String> {
    let inner = raw
        .strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .ok_or_else(|| format!("expected quoted string, got {raw:?}"))?;
    let mut out = String::with_capacity(inner.len());
    let mut cs = inner.chars();
    while let Some(ch) = cs.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match cs.next() {
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('u') => {
                if cs.next() != Some('{') {
                    return Err(format!("bad \\u escape in {raw:?}"));
                }
                let mut hex = String::new();
                for c in cs.by_ref() {
                    if c == '}' {
                        break;
                    }
                    hex.push(c);
                }
                let code = u32::from_str_radix(&hex, 16).map_err(|e| format!("bad hex escape in {raw:?}: {e}"))?;
                let c = char::from_u32(code).ok_or_else(|| format!("invalid codepoint {code:#x}"))?;
                out.push(c);
            }
            Some(c) => return Err(format!("unknown escape \\{c} in {raw:?}")),
            None => return Err(format!("dangling backslash in {raw:?}")),
        }
    }
    Ok(out)
}

fn read_block_lines(lines: &[&str], pos: &mut usize) -> Result<String, String> {
    let mut buf = Vec::new();
    while *pos < lines.len() {
        let ln = lines[*pos];
        if ln.starts_with("@@") {
            break;
        }
        let body = ln
            .strip_prefix("| ")
            .ok_or_else(|| format!("line {}: expected `| ` prefix inside block, got {ln:?}", *pos + 1))?;
        buf.push(body);
        *pos += 1;
    }
    Ok(buf.join("\n"))
}

fn write_block_lines(out: &mut String, text: &str) {
    for ln in text.split('\n') {
        writeln!(out, "| {ln}").unwrap();
    }
}

// --- 1. call-templates.txt ---

#[derive(Clone, Debug)]
pub struct PhTemplate {
    pub id: String,
    pub kind: String,
    pub is_pred: bool,
    pub subject: Option<String>,
    pub params: Vec<String>,
    pub pattern: String,
}

#[derive(Clone, Debug)]
pub struct PrimTemplate {
    pub name: String,
    pub kind: String,
    pub pattern: String,
}

#[derive(Clone, Debug, Default)]
pub struct CallTemplates {
    pub phs: BTreeMap<String, PhTemplate>,
    pub prims: BTreeMap<String, PrimTemplate>,
}

impl CallTemplates {
    pub fn load(path: &Path) -> Result<Self, String> {
        let mut out = Self::default();
        if !path.exists() {
            return Ok(out);
        }
        let src = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        for (lno, raw) in src.lines().enumerate() {
            let ln = raw.trim();
            if ln.is_empty() || ln.starts_with('#') {
                continue;
            }
            if let Some(rest) = ln.strip_prefix("ph ") {
                let (head, pat_q) = rest
                    .split_once(" => ")
                    .ok_or_else(|| format!("{}:{}: missing ` => `", path.display(), lno + 1))?;
                let parts: Vec<&str> = head.split_whitespace().collect();
                if parts.len() != 3 {
                    return Err(format!("{}:{}: malformed ph line", path.display(), lno + 1));
                }
                let id = parts[0].strip_prefix('@').unwrap_or(parts[0]).to_string();
                let (is_pred, subject) = if let Some(s) = parts[1].strip_prefix("pred:") {
                    (true, if s == "-" { None } else { Some(s.to_string()) })
                } else {
                    (false, None)
                };
                let kind = parts[1].to_string();
                let p_inner = parts[2]
                    .strip_prefix('(')
                    .and_then(|s| s.strip_suffix(')'))
                    .ok_or_else(|| format!("{}:{}: expected (params)", path.display(), lno + 1))?;
                let params = if p_inner.is_empty() {
                    Vec::new()
                } else {
                    p_inner.split(',').map(|s| s.to_string()).collect()
                };
                let pattern = unesc_str(pat_q)?;
                out.phs.insert(id.clone(), PhTemplate { id, kind, is_pred, subject, params, pattern });
            } else if let Some(rest) = ln.strip_prefix("prim ") {
                let (head, pat_q) = rest
                    .split_once(" => ")
                    .ok_or_else(|| format!("{}:{}: missing ` => `", path.display(), lno + 1))?;
                let (name_q, kind) = head
                    .rsplit_once(' ')
                    .ok_or_else(|| format!("{}:{}: expected `prim \"Name\" kind => ...`", path.display(), lno + 1))?;
                let name = unesc_str(name_q)?;
                let pattern = unesc_str(pat_q)?;
                out.prims.insert(name.clone(), PrimTemplate { name, kind: kind.to_string(), pattern });
            } else {
                return Err(format!("{}:{}: unknown entry {ln:?}", path.display(), lno + 1));
            }
        }
        Ok(out)
    }

    pub fn save(&self, path: &Path) -> Result<(), String> {
        let mut out = String::from("# Name-keyed SpecTec @ph-* and $Prim ecmarkdown phrase templates\n\n");
        for t in self.phs.values() {
            writeln!(out, "ph @{} {} ({}) => {}", t.id, t.kind, t.params.join(","), esc_str(&t.pattern)).unwrap();
        }
        if !self.prims.is_empty() {
            out.push('\n');
            for p in self.prims.values() {
                writeln!(out, "prim {} {} => {}", esc_str(&p.name), p.kind, esc_str(&p.pattern)).unwrap();
            }
        }
        std::fs::write(path, out).map_err(|e| format!("{}: {e}", path.display()))
    }
}

// --- 2. grammar-meta.txt ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockLayout {
    pub key: ItemKey,
    pub grammar: GrammarId,
    pub indent: usize,
    pub fmt_ignore: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuleOverride {
    pub key: ItemKey,
    pub grammar: GrammarId,
    pub lhs: String,
    pub spectec_rule: String,
    pub html_rule: String,
}

#[derive(Clone, Debug, Default)]
pub struct GrammarMeta {
    pub blocks: BTreeMap<ItemKey, BlockLayout>,
    pub spectec_only_blocks: BTreeMap<ItemKey, GrammarId>,
    pub overrides: BTreeMap<(ItemKey, String), RuleOverride>,
}

impl GrammarMeta {
    pub fn load(path: &Path) -> Result<Self, String> {
        let mut out = Self::default();
        if !path.exists() {
            return Ok(out);
        }
        let src = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let lines: Vec<&str> = src.lines().collect();
        let mut i = 0;
        while i < lines.len() {
            let ln = lines[i].trim();
            i += 1;
            if ln.is_empty() || ln.starts_with('#') {
                continue;
            }
            if let Some(rest) = ln.strip_prefix("block ") {
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() < 3 {
                    return Err(format!("{}:{}: malformed block line", path.display(), i));
                }
                let key = ItemKey::parse_ref(parts[0])?;
                let grammar = GrammarId::parse(parts[1])?;
                let indent = parts[2]
                    .strip_prefix("indent=")
                    .and_then(|v| v.parse::<usize>().ok())
                    .ok_or_else(|| format!("{}:{}: bad indent", path.display(), i))?;
                let mut fmt_ignore = Vec::new();
                if let Some(fi) = parts.get(3) {
                    let list = fi
                        .strip_prefix("fmt_ignore=")
                        .ok_or_else(|| format!("{}:{}: bad fmt_ignore", path.display(), i))?;
                    for s in list.split(',').filter(|s| !s.is_empty()) {
                        fmt_ignore.push(s.parse::<usize>().map_err(|e| format!("{}:{}: {e}", path.display(), i))?);
                    }
                }
                out.blocks.insert(key.clone(), BlockLayout { key, grammar, indent, fmt_ignore });
            } else if let Some(rest) = ln.strip_prefix("spectec_only_block ") {
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() != 2 {
                    return Err(format!("{}:{}: malformed spectec_only_block", path.display(), i));
                }
                let key = ItemKey::parse_ref(parts[0])?;
                let grammar = GrammarId::parse(parts[1])?;
                out.spectec_only_blocks.insert(key, grammar);
            } else if let Some(rest) = ln.strip_prefix("@@rule_override ") {
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() != 3 {
                    return Err(format!("{}:{}: malformed @@rule_override", path.display(), i));
                }
                let key = ItemKey::parse_ref(parts[0])?;
                let grammar = GrammarId::parse(parts[1])?;
                let lhs = parts[2]
                    .strip_prefix('|')
                    .and_then(|s| s.strip_suffix('|'))
                    .ok_or_else(|| format!("{}:{}: expected |LHS|", path.display(), i))?
                    .to_string();
                if lines.get(i).map(|s| s.trim()) != Some("@@spectec") {
                    return Err(format!("{}:{}: expected @@spectec", path.display(), i + 1));
                }
                i += 1;
                let spectec_rule = read_block_lines(&lines, &mut i)?;
                if lines.get(i).map(|s| s.trim()) != Some("@@html") {
                    return Err(format!("{}:{}: expected @@html", path.display(), i + 1));
                }
                i += 1;
                let html_rule = read_block_lines(&lines, &mut i)?;
                if lines.get(i).map(|s| s.trim()) != Some("@@end") {
                    return Err(format!("{}:{}: expected @@end", path.display(), i + 1));
                }
                i += 1;
                out.overrides.insert(
                    (key.clone(), lhs.clone()),
                    RuleOverride { key, grammar, lhs, spectec_rule, html_rule },
                );
            } else {
                return Err(format!("{}:{}: unknown directive {ln:?}", path.display(), i));
            }
        }
        Ok(out)
    }

    pub fn save(&self, path: &Path) -> Result<(), String> {
        let mut out = String::from("# Grammar definition block layout & errata rule overrides\n\n");
        for b in self.blocks.values() {
            let fi = if b.fmt_ignore.is_empty() {
                String::new()
            } else {
                let xs: Vec<_> = b.fmt_ignore.iter().map(|n| n.to_string()).collect();
                format!(" fmt_ignore={}", xs.join(","))
            };
            writeln!(out, "block {} {} indent={}{fi}", b.key.fmt_ref(), b.grammar.as_str(), b.indent).unwrap();
        }
        if !self.spectec_only_blocks.is_empty() {
            out.push('\n');
            for (k, g) in &self.spectec_only_blocks {
                writeln!(out, "spectec_only_block {} {}", k.fmt_ref(), g.as_str()).unwrap();
            }
        }
        if !self.overrides.is_empty() {
            out.push('\n');
            for ov in self.overrides.values() {
                writeln!(out, "@@rule_override {} {} |{}|", ov.key.fmt_ref(), ov.grammar.as_str(), ov.lhs).unwrap();
                writeln!(out, "@@spectec").unwrap();
                write_block_lines(&mut out, &ov.spectec_rule);
                writeln!(out, "@@html").unwrap();
                write_block_lines(&mut out, &ov.html_rule);
                writeln!(out, "@@end\n").unwrap();
            }
        }
        std::fs::write(path, out).map_err(|e| format!("{}: {e}", path.display()))
    }
}

// --- 3. item-meta.txt ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemKindMeta {
    Alg { base: usize, close: usize },
    Row { base: usize, close: usize },
    Eq { indent: usize },
    Early { indent: usize, layout: String },
    Twin { of: ItemKey },
    Tmpl { param: String, base: usize, close: usize },
    TmplInst,
    SpectecOnlyDef,
    SpectecOnlyRow,
}

#[derive(Clone, Debug, Default)]
pub struct ItemMeta {
    pub items: BTreeMap<(String, ItemKey), ItemKindMeta>,
}

impl ItemMeta {
    pub fn load(path: &Path) -> Result<Self, String> {
        let mut out = Self::default();
        if !path.exists() {
            return Ok(out);
        }
        let src = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        for (lno, raw) in src.lines().enumerate() {
            let ln = raw.trim();
            if ln.is_empty() || ln.starts_with('#') {
                continue;
            }
            let ps: Vec<&str> = ln.split_whitespace().collect();
            let err = |msg: &str| format!("{}:{}: {msg}", path.display(), lno + 1);
            if ps.len() < 2 {
                return Err(err("too few fields"));
            }
            let key = ItemKey::parse_ref(ps[1])?;
            let val = match ps[0] {
                "alg" => {
                    let base = ps.get(2).and_then(|s| s.strip_prefix("base=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad base"))?;
                    let close = ps.get(3).and_then(|s| s.strip_prefix("close=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad close"))?;
                    ItemKindMeta::Alg { base, close }
                }
                "row" => {
                    let base = ps.get(2).and_then(|s| s.strip_prefix("base=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad base"))?;
                    let close = ps.get(3).and_then(|s| s.strip_prefix("close=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad close"))?;
                    ItemKindMeta::Row { base, close }
                }
                "eq" => {
                    let indent = ps.get(2).and_then(|s| s.strip_prefix("indent=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad indent"))?;
                    ItemKindMeta::Eq { indent }
                }
                "early" => {
                    let indent = ps.get(2).and_then(|s| s.strip_prefix("indent=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad indent"))?;
                    let layout = ps.get(3).and_then(|s| s.strip_prefix("layout=")).ok_or_else(|| err("bad layout"))?.to_string();
                    ItemKindMeta::Early { indent, layout }
                }
                "twin" => {
                    let of_s = ps.get(2).and_then(|s| s.strip_prefix("of=")).ok_or_else(|| err("bad of="))?;
                    ItemKindMeta::Twin { of: ItemKey::parse_ref(of_s)? }
                }
                "tmpl" => {
                    let param = ps.get(2).and_then(|s| s.strip_prefix("param=")).ok_or_else(|| err("bad param="))?.to_string();
                    let base = ps.get(3).and_then(|s| s.strip_prefix("base=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad base"))?;
                    let close = ps.get(4).and_then(|s| s.strip_prefix("close=")).and_then(|v| v.parse().ok()).ok_or_else(|| err("bad close"))?;
                    ItemKindMeta::Tmpl { param, base, close }
                }
                "tmpl_inst" => ItemKindMeta::TmplInst,
                "spectec_only_def" => ItemKindMeta::SpectecOnlyDef,
                "spectec_only_row" => ItemKindMeta::SpectecOnlyRow,
                other => return Err(err(&format!("unknown tag {other}"))),
            };
            out.items.insert((ps[0].to_string(), key), val);
        }
        Ok(out)
    }

    pub fn save(&self, path: &Path) -> Result<(), String> {
        let mut out = String::from("# Keyed item metadata linking spec/spectec items and spec.html slots\n\n");
        for ((tag, key), val) in &self.items {
            match val {
                ItemKindMeta::Alg { base, close } => writeln!(out, "{tag} {} base={base} close={close}", key.fmt_ref()).unwrap(),
                ItemKindMeta::Row { base, close } => writeln!(out, "{tag} {} base={base} close={close}", key.fmt_ref()).unwrap(),
                ItemKindMeta::Eq { indent } => writeln!(out, "{tag} {} indent={indent}", key.fmt_ref()).unwrap(),
                ItemKindMeta::Early { indent, layout } => writeln!(out, "{tag} {} indent={indent} layout={layout}", key.fmt_ref()).unwrap(),
                ItemKindMeta::Twin { of } => writeln!(out, "{tag} {} of={}", key.fmt_ref(), of.fmt_ref()).unwrap(),
                ItemKindMeta::Tmpl { param, base, close } => writeln!(out, "{tag} {} param={param} base={base} close={close}", key.fmt_ref()).unwrap(),
                ItemKindMeta::TmplInst | ItemKindMeta::SpectecOnlyDef | ItemKindMeta::SpectecOnlyRow => {
                    writeln!(out, "{tag} {}", key.fmt_ref()).unwrap()
                }
            }
        }
        std::fs::write(path, out).map_err(|e| format!("{}: {e}", path.display()))
    }
}

// --- 4. step-patches.txt ---

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StepPatch {
    pub kind: String,
    pub key: ItemKey,
    pub path: String,
    pub spectec: String,
    pub html: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StepAttr {
    pub kind: String,
    pub key: ItemKey,
    pub path: String,
    pub attrs: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StepCont {
    pub kind: String,
    pub key: ItemKey,
    pub path: String,
    pub cont: String,
}

#[derive(Clone, Debug, Default)]
pub struct StepPatches {
    /// Keyed by (kind, key, step_path_in_html_or_tree)
    pub attrs: BTreeMap<(String, ItemKey, String), StepAttr>,
    pub conts: BTreeMap<(String, ItemKey, String), StepCont>,
    /// Keyed by (kind, key, block_range_path) e.g. `root:3..5` or `root/0:then:1..2` or `body`
    pub patches: BTreeMap<(String, ItemKey, String), StepPatch>,
}

impl StepPatches {
    pub fn load(path: &Path) -> Result<Self, String> {
        let mut out = Self::default();
        if !path.exists() {
            return Ok(out);
        }
        let src = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let lines: Vec<&str> = src.lines().collect();
        let mut i = 0;
        while i < lines.len() {
            let ln = lines[i].trim();
            i += 1;
            if ln.is_empty() || ln.starts_with('#') {
                continue;
            }
            if let Some(rest) = ln.strip_prefix("attr ") {
                let mut parts = rest.splitn(4, ' ');
                let kind = parts.next().ok_or("bad attr")?.to_string();
                let key = ItemKey::parse_ref(parts.next().ok_or("bad attr key")?)?;
                let spath = parts.next().ok_or("bad attr path")?.to_string();
                let attrs = unesc_str(parts.next().ok_or("bad attr str")?)?;
                out.attrs.insert((kind.clone(), key.clone(), spath.clone()), StepAttr { kind, key, path: spath, attrs });
            } else if let Some(rest) = ln.strip_prefix("@@cont ") {
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() != 3 {
                    return Err(format!("{}:{}: malformed @@cont", path.display(), i));
                }
                let kind = parts[0].to_string();
                let key = ItemKey::parse_ref(parts[1])?;
                let spath = parts[2].to_string();
                let cont = read_block_lines(&lines, &mut i)?;
                if lines.get(i).map(|s| s.trim()) != Some("@@end") {
                    return Err(format!("{}:{}: expected @@end", path.display(), i + 1));
                }
                i += 1;
                out.conts.insert((kind.clone(), key.clone(), spath.clone()), StepCont { kind, key, path: spath, cont });
            } else if let Some(rest) = ln.strip_prefix("@@patch ") {
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() != 3 {
                    return Err(format!("{}:{}: malformed @@patch", path.display(), i));
                }
                let kind = parts[0].to_string();
                let key = ItemKey::parse_ref(parts[1])?;
                let ppath = parts[2].to_string();
                if lines.get(i).map(|s| s.trim()) != Some("@@spectec") {
                    return Err(format!("{}:{}: expected @@spectec", path.display(), i + 1));
                }
                i += 1;
                let spectec = read_block_lines(&lines, &mut i)?;
                if lines.get(i).map(|s| s.trim()) != Some("@@html") {
                    return Err(format!("{}:{}: expected @@html", path.display(), i + 1));
                }
                i += 1;
                let html = read_block_lines(&lines, &mut i)?;
                if lines.get(i).map(|s| s.trim()) != Some("@@end") {
                    return Err(format!("{}:{}: expected @@end", path.display(), i + 1));
                }
                i += 1;
                out.patches.insert(
                    (kind.clone(), key.clone(), ppath.clone()),
                    StepPatch { kind, key, path: ppath, spectec, html },
                );
            } else {
                return Err(format!("{}:{}: unknown entry {ln:?}", path.display(), i));
            }
        }
        Ok(out)
    }

    pub fn save(&self, path: &Path) -> Result<(), String> {
        let mut out = String::from("# Step attributes, continuation lines, and bidirectional AST<->HTML patches\n\n");
        for a in self.attrs.values() {
            writeln!(out, "attr {} {} {} {}", a.kind, a.key.fmt_ref(), a.path, esc_str(&a.attrs)).unwrap();
        }
        if !self.attrs.is_empty() && (!self.conts.is_empty() || !self.patches.is_empty()) {
            out.push('\n');
        }
        for c in self.conts.values() {
            writeln!(out, "@@cont {} {} {}", c.kind, c.key.fmt_ref(), c.path).unwrap();
            write_block_lines(&mut out, &c.cont);
            writeln!(out, "@@end").unwrap();
        }
        if !self.conts.is_empty() && !self.patches.is_empty() {
            out.push('\n');
        }
        for p in self.patches.values() {
            writeln!(out, "@@patch {} {} {}", p.kind, p.key.fmt_ref(), p.path).unwrap();
            writeln!(out, "@@spectec").unwrap();
            write_block_lines(&mut out, &p.spectec);
            writeln!(out, "@@html").unwrap();
            write_block_lines(&mut out, &p.html);
            writeln!(out, "@@end\n").unwrap();
        }
        std::fs::write(path, out).map_err(|e| format!("{}: {e}", path.display()))
    }
}

pub fn check_all_used<T: Ord + std::fmt::Debug>(defined: &BTreeSet<T>, used: &BTreeSet<T>, what: &str) -> Result<(), String> {
    let unused: Vec<_> = defined.difference(used).take(10).collect();
    if !unused.is_empty() {
        return Err(format!("{} unused {what} metadata entries (first: {:?})", defined.difference(used).count(), unused));
    }
    Ok(())
}
