//! The host and implementation requirements as Lean modules
//! (`Ecma.Gen.Host*`, terms of `Ecma.Notation.Host`): every
//! paragraph holding a requirement, its sentences and the white space between
//! them, sharded at `SHARD` requirements or `SHARD_BYTES` bytes. The host's
//! phrase rows and names are interned into the main declarations.

use crate::data::Data;
use crate::grammar::Grammar;
use crate::host::{Duty, HookRef, HostReq, Modal, Post, Premise, Req, Why};
use crate::lean::{ch, cond, expr, holes, parts, s, stmt, ty, HEADER};
use crate::overlay::{HostLaw, LawClass};
use crate::spec::Spec;
use std::collections::HashMap;
use std::fmt::Write;
use std::path::Path;

/// The most requirements a module holds.
const SHARD: usize = 300;
/// The most bytes a module holds.
const SHARD_BYTES: usize = 300_000;

fn opt<T>(x: &Option<T>, f: impl Fn(&T) -> String) -> String {
    match x {
        Some(v) => format!("(some {})", f(v)),
        None => "none".into(),
    }
}

fn b(x: bool) -> &'static str {
    if x {
        "true"
    } else {
        "false"
    }
}

fn modal(m: Modal) -> &'static str {
    match m {
        Modal::Must => ".must",
        Modal::MustNot => ".mustNot",
        Modal::MustNever => ".mustNever",
        Modal::MustAlso => ".mustAlso",
        Modal::Shall => ".shall",
        Modal::ShallNot => ".shallNot",
        Modal::Indicative => ".indicative",
    }
}

fn premise(p: &Premise) -> String {
    match p {
        Premise::If(c, t) => format!("(.if_ {} {})", cond(c), b(*t)),
        Premise::EachTime(e, k) => format!("(.eachTime {} {})", expr(e), b(*k)),
        Premise::Unless(c) => format!("(.unless {})", cond(c)),
        Premise::When(c) => format!("(.when {})", cond(c)),
        Premise::Otherwise => ".otherwise".into(),
    }
}

fn duty(d: &Duty) -> String {
    match d {
        Duty::Return(t) => format!("(.ret {})", ty(t)),
        Duty::Be(t) => format!("(.be {})", ty(t)),
        Duty::Phrase(p, hs) => format!("(.phrase {p} {})", holes(hs)),
    }
}

fn post((f, c): &(Post, crate::ast::Cond)) -> String {
    let f = match f {
        Post::CommaUnless => ".commaUnless",
        Post::Unless => ".unless",
        Post::If => ".if_",
    };
    format!("({f}, {})", cond(c))
}

fn req(r: &Req) -> String {
    match r {
        Req::Must(m) => format!(
            "(.must {{ premise := {}, subject := {}, modal := {}, duty := {}, post := {}, either := {}, colon := {} }})",
            opt(&m.premise, premise),
            expr(&m.subject),
            modal(m.modal),
            duty(&m.duty),
            opt(&m.post, post),
            b(m.either),
            b(m.colon)
        ),
        Req::Holds(p, c) => format!("(.holds {} {})", opt(p, cond), cond(c)),
        Req::Step(st) => format!("(.step {})", stmt(st)),
        Req::Default(c, e) => format!("(.default_ {c} {})", expr(e)),
        Req::Phrase(p, hs) => format!("(.phrase {p} {})", holes(hs)),
        Req::Prose(c, ps) => format!("(.prose {} {})", ch(c), parts(ps)),
    }
}

fn why(w: Why) -> &'static str {
    match w {
        Why::Modal => ".modal",
        Why::Item => ".item",
        Why::Default => ".default_",
        Why::Indicative => ".indicative",
    }
}

fn hook(h: &Option<HookRef>) -> String {
    opt(h, |h| match h {
        HookRef::Alg(c) => format!("(.alg {c})"),
        HookRef::Method(m) => format!("(.method {m})"),
        HookRef::Every => ".every".into(),
    })
}

fn host_req(r: &HostReq) -> String {
    format!("{{ why := {}, cap := {}, req := {} }}", why(r.why), b(r.s.cap), req(&r.s.req))
}

fn disp(l: &HostLaw) -> String {
    let c = match l.class {
        LawClass::Law => ".law",
        LawClass::Theorem => ".theorem_",
        LawClass::Advice => ".advice",
        LawClass::Scope => ".scope",
        LawClass::Syntax => ".syntax_",
        LawClass::Nonfunctional => ".nonfunctional",
    };
    format!("{{ cls := {c}, law := {}, reason := {} }}", opt(&l.law, |f| s(f)), s(&l.reason))
}

/// The module naming each law disposition's `Host.WF` field: a field that does not exist
/// fails its build.
pub fn law_refs(laws: &[HostLaw]) -> String {
    let mut o = format!("module\n\npublic import Ecma.Host.Laws\n\n/-! {HEADER} -/\n\n/-! The `Host.WF` fields the host laws of class law name. -/\n\nnamespace Ecma.Gen\n\n");
    let mut seen = std::collections::BTreeSet::new();
    for l in laws {
        if let Some(f) = l.law.as_ref().filter(|f| seen.insert(f.as_str())) {
            writeln!(o, "example := @Ecma.Host.WF.{f}").unwrap();
        }
    }
    if !seen.is_empty() {
        o.push('\n');
    }
    o.push_str("end Ecma.Gen\n");
    o
}

/// Builds the requirements over `dt`'s declarations and writes their modules
/// to `dir`; a summary.
pub fn emit(dir: &Path, html: &str, sp: &Spec, g: &Grammar, dt: &mut Data) -> Result<String, String> {
    let h = crate::host::build_on(html, sp, g, std::mem::take(&mut dt.decls), &dt.env);
    if !h.disp_errors.is_empty() {
        return Err(h.disp_errors.join("\n"));
    }
    let laws = &g.overlay.host_laws;
    let (paras, reqs) = (h.paras, h.reqs);
    dt.decls = h.decls;
    let mut by_para: Vec<Vec<&HostReq>> = vec![Vec::new(); paras.len()];
    for r in &reqs {
        by_para[r.para].push(r);
    }
    let mut seen: HashMap<usize, usize> = HashMap::new();
    let mut shards: Vec<(Vec<String>, String, usize)> = Vec::new();
    for (pi, pa) in paras.iter().enumerate() {
        let Some(c) = pa.clause else { continue };
        let k = seen.entry(c).or_default();
        let idx = *k;
        *k += 1;
        let rs = &by_para[pi];
        if rs.is_empty() {
            continue;
        }
        let mut sents = Vec::new();
        for (si, &(a, e)) in pa.sents.iter().enumerate() {
            let next = pa.sents.get(si + 1).map(|x| x.0).unwrap_or(pa.raw.len());
            let sent = match rs.iter().find(|r| r.sent == si) {
                Some(r) => match r.disp {
                    Some(l) => format!("(.disp {} {})", disp(&laws[l]), s(&pa.raw[a..e])),
                    None => format!("(.req {})", host_req(r)),
                },
                None => format!("(.text {})", s(&pa.raw[a..e])),
            };
            sents.push(format!("({sent}, {})", s(&pa.raw[e..next])));
        }
        let cl = &sp.clauses[c];
        let vars = format!("#[{}]", rs[0].vars.names.iter().map(|v| s(v)).collect::<Vec<_>>().join(", "));
        let name = format!("p{}_{idx}", crate::lean::cid(c));
        let def = format!(
            "/-- {} ¶{idx} (§{}), spec.html:{} -/\ndef {name} : HostPara := {{\n  clause := {}\n  idx := {idx}\n  hook := {}\n  vars := {vars}\n  lead := {}\n  sents := [\n    {}] }}\n\n",
            cl.id,
            cl.number,
            pa.line,
            crate::lean::cid(c),
            hook(&rs[0].hook),
            s(&pa.raw[..pa.sents[0].0]),
            sents.join(",\n    ")
        );
        match shards.last_mut() {
            Some((names, text, n)) if *n + rs.len() <= SHARD && text.len() + def.len() <= SHARD_BYTES => {
                names.push(name);
                text.push_str(&def);
                *n += rs.len();
            }
            _ => shards.push((vec![name], def, rs.len())),
        }
    }
    let mut mods = Vec::new();
    for (i, (names, text, _)) in shards.iter().enumerate() {
        let m = format!("Host{}", i + 1);
        let mut o = String::new();
        writeln!(o, "module\n\npublic import Ecma.Notation.Host\n\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen.{m}\n\nopen Ecma\n").unwrap();
        o.push_str(text);
        writeln!(o, "/-- The paragraphs of this module, in document order. -/\ndef paras : List HostPara := [{}]\n\nend Ecma.Gen.{m}", names.join(", ")).unwrap();
        std::fs::write(dir.join(format!("{m}.lean")), o).map_err(|e| e.to_string())?;
        mods.push(m);
    }
    let mut o = String::from("module\n\n");
    for m in &mods {
        writeln!(o, "public import Ecma.Gen.{m}").unwrap();
    }
    writeln!(o, "\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen\n\nopen Ecma\n").unwrap();
    let all = mods.iter().map(|m| format!("{m}.paras")).collect::<Vec<_>>().join(",\n    ");
    writeln!(o, "/-- Every paragraph holding a host or implementation requirement, by module. -/\ndef hostParas : List (List HostPara) := [\n    {all}]\n\nend Ecma.Gen").unwrap();
    std::fs::write(dir.join("HostIndex.lean"), o).map_err(|e| e.to_string())?;
    std::fs::write(dir.join("HostLawRefs.lean"), law_refs(laws)).map_err(|e| e.to_string())?;
    let np = by_para.iter().filter(|r| !r.is_empty()).count();
    Ok(format!("wrote {} host modules ({} requirements in {np} paragraphs, {} dispositioned), HostIndex.lean and HostLawRefs.lean", mods.len(), reqs.len(), reqs.iter().filter(|r| r.disp.is_some()).count()))
}
