//! Section 29 as Lean data (`Ecma.Gen.Memory*`, in the shape of
//! `Ecma.Notation.Memory`): the declaration tables extended by the names the
//! section adds, its lexicons and phrase rows, and its blocks, one definition per
//! clause, sharded at `SHARD_BYTES`.

use crate::ast::{ConnForm, Expr, Id};
use crate::data::Data;
use crate::decls::Table;
use crate::grammar::Grammar;
use crate::lean::{array, cond, expr, hole, meaning, parts, phrase_cat, piece, s, ty, HEADER};
use crate::memmodel::*;
use crate::spec::Spec;
use std::collections::HashMap;
use std::fmt::Write;
use std::path::Path;

/// The most bytes of clause definitions a data module holds.
pub const SHARD_BYTES: usize = 300_000;

/// Channel (c)'s kind of the section's prose sentences.
pub const INFORMATIVE: &str = "informative";

fn list<T>(xs: &[T], f: impl Fn(&T) -> String) -> String {
    format!("[{}]", xs.iter().map(f).collect::<Vec<_>>().join(", "))
}

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

fn conn(f: &ConnForm) -> &'static str {
    match f {
        ConnForm::Plain => ".plain",
        ConnForm::Comma => ".comma",
        ConnForm::OrIf => ".orIf",
        ConnForm::Following => ".following",
    }
}

fn tag(t: &TermTag) -> String {
    match t {
        TermTag::Dfn(v) => format!("(.dfn {})", opt(v, |x| s(x))),
        TermTag::Em => ".em".into(),
    }
}

fn term(t: &Term) -> String {
    format!("⟨{}, {}⟩", tag(&t.tag), s(&t.words))
}

fn pname(n: &PName) -> String {
    match n {
        PName::Lex(i) => format!("(.lex {i})"),
        PName::Term(i, t) => format!("(.term {i} {})", tag(t)),
        PName::Xref(e) => format!("(.xref {})", expr(e)),
    }
}

fn rexpr(e: &MExpr) -> String {
    match e {
        MExpr::E(x) => format!("(.e {})", expr(x)),
        MExpr::In(f, x) => format!("(.in_ {} {})", expr(f), expr(x)),
        MExpr::Pair(x, y) => format!("(.pair {} {})", expr(x), expr(y)),
    }
}

fn range(k: &RangeRel) -> &'static str {
    match k {
        RangeRel::Equal => ".equal",
        RangeRel::Overlapping => ".overlapping",
        RangeRel::Disjoint => ".disjoint",
    }
}

fn verb(v: &Verb) -> &'static str {
    match v {
        Verb::Has => ".has",
        Verb::Is => ".is",
        Verb::AreIn => ".areIn",
    }
}

fn oexpr(e: &Option<Expr>) -> String {
    opt(e, expr)
}

fn atom(a: &Atom) -> String {
    match a {
        Atom::Rel(r, x, y, e) => format!("(.rel {r} {} {} {})", expr(x), expr(y), oexpr(e)),
        Atom::Exists(v, q, t, x, dom, c) => {
            let q = match q {
                Quant::Some => ".some",
                Quant::An => ".an",
                Quant::A => ".a",
                Quant::No => ".no",
            };
            let dom = opt(dom, |d| match d {
                Dom::In(e) => format!("(.in_ {})", expr(e)),
                Dom::HasInRange(e) => format!("(.hasInRange {})", expr(e)),
            });
            format!("(.exists_ {} {q} {} {x} {dom} {})", b(*v), ty(t), mcond(c))
        }
        Atom::Not(both, c) => format!("(.not {} {})", b(*both), mcond(c)),
        Atom::Same(neg, x, y, t) => format!("(.same {} {} {} {})", b(*neg), expr(x), expr(y), ty(t)),
        Atom::Contains(x, both, ys) => format!("(.contains {} {} {})", rexpr(x), b(*both), list(ys, rexpr)),
        Atom::Ranges(neg, k, x, y) => format!("(.ranges {} {} {} {})", b(*neg), range(k), expr(x), expr(y)),
        Atom::Before(x, y, l) => format!("(.before {} {} {})", expr(x), expr(y), expr(l)),
        Atom::Following(f) => format!(
            "(.following {})",
            match f {
                Following::Any(c) => format!("(.any {})", b(*c)),
                Following::All(c) => format!("(.all {})", b(*c)),
                Following::The => ".the".into(),
            }
        ),
        Atom::FollowingAlg(e) => format!("(.followingAlg {})", expr(e)),
        Atom::Pred(xs, v, n, e) => format!("(.pred {} {} {} {})", list(xs, expr), verb(v), pname(n), oexpr(e)),
        Atom::InRange(x, y) => format!("(.inRange {} {})", expr(x), expr(y)),
        Atom::NoCycle(rs, x) => format!("(.noCycle {} {})", list(rs, |r| r.to_string()), expr(x)),
        Atom::Admits(x, a, r, po) => format!("(.admits {} {} {r} {})", oexpr(x), s(a), b(*po)),
        Atom::IsA(x, either, a, t) => format!("(.isA {} {} {} {})", expr(x), b(*either), s(a), ty(t)),
        Atom::Core(c) => format!("(.core {})", cond(c)),
        Atom::Phrase(p, hs) => format!("(.phrase {p} {})", list(hs, mhole)),
    }
}

fn mcond(c: &MCond) -> String {
    match c {
        MCond::Atom(a) => format!("(.atom {})", atom(a)),
        MCond::And(f, cs) => format!("(.and {} {})", conn(f), list(cs, mcond)),
        MCond::Or(f, cs) => format!("(.or {} {})", conn(f), list(cs, mcond)),
    }
}

fn mhole(h: &MHole) -> String {
    match h {
        MHole::H(x) => format!("(.h {})", hole(x)),
        MHole::Term(t) => format!("(.term {})", term(t)),
        MHole::Rel(r) => format!("(.rel {r})"),
        MHole::Name(n) => format!("(.name {})", pname(n)),
        MHole::C(c) => format!("(.c {})", mcond(c)),
        MHole::E(e) => format!("(.e {})", rexpr(e)),
        MHole::T(t) => format!("(.t {})", ty(t)),
        MHole::W(i) => format!("(.w {i})"),
    }
}

fn binder(x: &Binder) -> String {
    match x {
        Binder::Pair(t, x, y, c) => format!("(.pair {} {x} {y} {})", ty(t), opt(c, mcond)),
        Binder::PairIn(t, x, y, e) => format!("(.pairIn {} {x} {y} {})", ty(t), expr(e)),
        Binder::Each(t, x, e) => format!("(.each {} {x} {})", ty(t), expr(e)),
        Binder::Elem(x, e) => format!("(.elem {x} {})", expr(e)),
        Binder::One(a, t, x) => format!("(.one {} {} {x})", s(a), ty(t)),
    }
}

fn formula(f: &Formula) -> String {
    match f {
        Formula::Rule(a, c) => format!("(.rule {} {})", atom(a), mcond(c)),
        Formula::Holds(c) => format!("(.holds {})", mcond(c)),
        Formula::Implies(t, c, d) => format!("(.implies {} {} {})", b(*t), mcond(c), mcond(d)),
    }
}

fn relkind(k: &RelKind) -> String {
    match k {
        RelKind::Least(t) => format!("(.least {})", ty(t)),
        RelKind::Host(t) => format!("(.host {})", ty(t)),
        RelKind::Total(t, e) => format!("(.total {} {})", ty(t), expr(e)),
        RelKind::Function(t, e, u, f) => format!("(.function {} {} {} {})", ty(t), expr(e), ty(u), expr(f)),
    }
}

/// Emits the Lean of the section's blocks: clause definitions by name, and counts.
struct Em<'a> {
    /// `Spec::algs` index -> its `AlgId` in the data
    algs: &'a HashMap<usize, (usize, usize)>,
    /// the prose sentences' channel
    informative: Id,
    /// clause definitions, children before parents: name, source
    defs: Vec<(String, String)>,
    sents: usize,
    prose: usize,
    rows: usize,
}

impl Em<'_> {
    fn sent(&mut self, x: &Sent) -> String {
        self.sents += 1;
        match x {
            Sent::SortUnion(a, t, alts, rec) => format!(
                "(.sortUnion {} {} {} {})",
                s(a),
                term(t),
                list(alts, |(a, r)| format!(
                    "({}, {})",
                    s(a),
                    match r {
                        SortRef::Term(t) => format!("(.term {})", term(t)),
                        SortRef::Ty(t) => format!("(.ty {})", ty(t)),
                    }
                )),
                b(*rec)
            ),
            Sent::RelDef(x, r, t, k) => format!("(.relDef {x} {r} {} {})", tag(t), relkind(k)),
            Sent::PredDef(v, x, vb, n, c) => format!("(.predDef {} {} {} {} {})", b(*v), opt(x, |x| x.to_string()), verb(vb), pname(n), mcond(c)),
            Sent::RangeDef(k, c) => format!("(.rangeDef {} {})", range(k), mcond(c)),
            Sent::For(bs, f) => format!("(.for_ {} {})", list(bs, binder), formula(f)),
            Sent::Formula(f) => format!("(.formula {})", formula(f)),
            Sent::Phrase(p, hs) => format!("(.phrase {p} {})", list(hs, mhole)),
            Sent::Prose(ps) => {
                self.prose += 1;
                format!("(.prose (.annotated {} none) {})", self.informative, parts(ps))
            }
        }
    }

    fn sents(&mut self, xs: &[Sent]) -> String {
        format!("[{}]", xs.iter().map(|x| self.sent(x)).collect::<Vec<_>>().join(", "))
    }

    fn table(&mut self, t: &FieldTable) -> String {
        self.rows += t.rows.len();
        let rows = list(&t.rows, |r| format!("{{ field := {}, ty := {}, desc := {} }}", r.field, ty(&r.ty), s(&r.desc)));
        format!("{{ id := {}, caption := {}, heads := {}, rows := {rows} }}", s(&t.id), s(&t.caption), list(&t.heads, |h| s(h)))
    }

    fn blocks(&mut self, bs: &[Block]) -> Result<String, String> {
        let mut out = Vec::new();
        for x in bs {
            out.push(self.block(x)?);
        }
        Ok(format!("[{}]", out.join(",\n  ")))
    }

    fn block(&mut self, x: &Block) -> Result<String, String> {
        Ok(match x {
            Block::Clause { indent, attrs, vars, kids } => {
                let id = crate::spec::attr(attrs, "id").ok_or_else(|| format!("a clause without an id: {attrs}"))?;
                let kids = self.blocks(kids)?;
                let vars = format!("#[{}]", vars.iter().map(|v| s(v)).collect::<Vec<_>>().join(", "));
                let name = format!("«{id}»");
                self.defs.push((name.clone(), format!("/-- `{id}` -/\ndef {name} : Block := .clause {indent} {} {vars}\n  {kids}\n", s(attrs))));
                name
            }
            Block::Para { indent, sents } => format!("(.para {indent} {})", self.sents(sents)),
            Block::Text { indent, sents } => format!("(.text {indent} {})", self.sents(sents)),
            Block::List { indent, items } => {
                let mut lis = Vec::new();
                for li in items {
                    lis.push(match &li.inline {
                        Some(ss) => format!("(.inline {})", self.sents(ss)),
                        None => format!("(.block {})", self.blocks(&li.kids)?),
                    });
                }
                format!("(.list {indent} [{}])", lis.join(",\n    "))
            }
            Block::Table { indent, table } => format!("(.table {indent} {})", self.table(table)),
            Block::Note { indent, lines } => format!("(.note {indent} {})", list(lines, |l| s(l))),
            Block::Alg { indent, alg } => {
                let (c, k) = self.algs.get(alg).ok_or("an emu-alg of section 29 not in the data")?;
                format!("(.alg {indent} ⟨{c}, {k}⟩)")
            }
            Block::Heading(ls) => format!("(.heading {})", list(ls, |l| s(l))),
            Block::Raw(l) => format!("(.raw {})", s(l)),
            Block::Blank => ".blank".into(),
        })
    }
}

fn rpiece(p: &MPiece) -> String {
    match p {
        MPiece::Word(w) => format!(".word {}", s(w)),
        MPiece::Glue => ".glue".into(),
        MPiece::Hole(c) => format!(".hole {}", s(c)),
        MPiece::Choice(alts) => format!(".choice {}", list(alts, |a| list(a, rpiece))),
    }
}

/// A table's names beyond the first `n`, appended to the data's.
fn ext(field: &str, t: &Table, n: usize, out: &mut Vec<String>) {
    if t.names.len() > n {
        out.push(format!("{field} := Ecma.Gen.decls.{field} ++ {}", array(t.names[n..].iter().map(|x| s(x)).collect())));
    }
}

const MODULE_HEAD: &str = "module\n\npublic import Ecma.Notation.Memory\n";

/// Adds the names section 29 interns to `d`'s frozen tables (phrases, primitives, sorts, fields,
/// enums) after its own, so the index files freeze their ids too.
pub fn freeze(html: &str, sp: &Spec, g: &Grammar, d: &mut crate::decls::Decls) -> Result<(), String> {
    let m = build_on(html, sp, g, d.clone())?.d;
    for (t, mt) in [(&mut d.prims, &m.prims), (&mut d.sorts, &m.sorts), (&mut d.fields, &m.fields), (&mut d.enums, &m.enums)] {
        for n in &mt.names[t.names.len()..] {
            t.intern(n);
        }
    }
    for (i, p) in m.phrases.iter().enumerate() {
        match d.phrases.get_mut(i) {
            Some(q) if q.template.is_empty() => {
                q.template = p.template.clone();
                q.meaning = p.meaning.clone();
            }
            Some(_) => {}
            None => {
                let k = d.phrase(p.cat, p.name, || p.template.clone());
                d.phrases[k].meaning = p.meaning.clone();
            }
        }
    }
    Ok(())
}

/// Writes `Memory*.lean` into `dir`; the summary.
pub fn write(html: &str, sp: &Spec, g: &Grammar, dt: &Data, dir: &Path) -> Result<String, String> {
    let base = &dt.decls;
    let mut doc = build_on(html, sp, g, base.clone())?;
    if print(&doc, sp) != doc.src {
        return Err("section 29 does not print back from its data".into());
    }
    let informative = doc.d.notes.intern(INFORMATIVE);
    let d = &doc.d;
    if d.clauses.names.len() != base.clauses.names.len() || d.ops != base.ops {
        return Err("section 29 changed the clause tables".into());
    }
    let algs: HashMap<usize, (usize, usize)> = dt
        .algs
        .iter()
        .filter(|a| !(a.hdr.kind == "sdo" && sp.algs[a.alg].prod.is_some()))
        .map(|a| (a.alg, (crate::lean::cid(a.clause), a.idx)))
        .collect();
    let mut em = Em { algs: &algs, informative, defs: Vec::new(), sents: 0, prose: 0, rows: 0 };
    let top = em.blocks(&doc.blocks)?;

    // the declaration tables: the data's, then the section's own names
    let mut fs = Vec::new();
    for (f, t, n) in [
        ("fields", &d.fields, &base.fields),
        ("enums", &d.enums, &base.enums),
        ("sdos", &d.sdos, &base.sdos),
        ("nts", &d.nts, &base.nts),
        ("prods", &d.prods, &base.prods),
        ("prims", &d.prims, &base.prims),
        ("sorts", &d.sorts, &base.sorts),
        ("methods", &d.methods, &base.methods),
        ("reasons", &d.reasons, &base.reasons),
        ("notes", &d.notes, &base.notes),
    ] {
        ext(f, t, n.names.len(), &mut fs);
    }
    let (np, ns, nq) = (base.phrases.len(), base.sdos.names.len(), base.prims.names.len());
    if d.phrases.len() > np {
        let rows = d.phrases[np..].iter().map(|p| format!("{{ cat := {}, template := {}, meaning := {} }}", phrase_cat(p.cat), list(&p.template, piece), meaning(&p.meaning)));
        fs.push(format!("phrases := Ecma.Gen.decls.phrases ++ {}", array(rows.collect())));
    }
    if d.sdos.names.len() > ns {
        fs.push(format!("sdoHeaders := Ecma.Gen.decls.sdoHeaders ++ {}", array(vec!["none".into(); d.sdos.names.len() - ns])));
    }
    if d.prims.names.len() > nq {
        fs.push(format!("primDocs := Ecma.Gen.decls.primDocs ++ {}", array(vec!["{ sig := \"\", meaning := \"\" }".into(); d.prims.names.len() - nq])));
    }
    let phrases = array(doc.md.phrases.iter().map(|p| format!("{{ cat := {}, name := {}, template := {} }}", s(p.cat), s(p.name), list(&p.template, rpiece))).collect());
    let names = |t: &Table| array(t.names.iter().map(|x| s(x)).collect());

    // shards of clause definitions, then the module with the tables and the section
    let mut shards: Vec<Vec<&(String, String)>> = vec![vec![]];
    let mut size = 0;
    for x in &em.defs {
        if size + x.1.len() > SHARD_BYTES && !shards.last().unwrap().is_empty() {
            shards.push(vec![]);
            size = 0;
        }
        size += x.1.len();
        shards.last_mut().unwrap().push(x);
    }
    let last = shards.pop().unwrap_or_default();
    let mut files: Vec<(String, String)> = Vec::new();
    let mut imports = String::new();
    for (i, sh) in shards.iter().enumerate() {
        let m = format!("MemoryClauses{}", i + 1);
        let mut o = format!("{MODULE_HEAD}{imports}");
        writeln!(o, "\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen.Memory\n\nopen Ecma Ecma.Memory\n").unwrap();
        for (_, src) in sh {
            writeln!(o, "{src}").unwrap();
        }
        writeln!(o, "end Ecma.Gen.Memory").unwrap();
        writeln!(imports, "public import Ecma.Gen.{m}").unwrap();
        files.push((m, o));
    }
    let mut o = format!("{MODULE_HEAD}public import Ecma.Gen.Decls\n{imports}");
    writeln!(o, "\n/-! {HEADER} -/\n\n@[expose] public section\n\nnamespace Ecma.Gen.Memory\n\nopen Ecma Ecma.Memory\n").unwrap();
    writeln!(o, "/-- The declaration tables: the data's, and the names section 29 adds. -/\ndef decls : Decls := {{ Ecma.Gen.decls with\n    {} }}\n", fs.join(",\n    ")).unwrap();
    writeln!(o, "/-- The relations and functions of a candidate execution. -/\ndef rels : Array String :=\n    {}\n", names(&doc.md.rels)).unwrap();
    writeln!(o, "/-- The predicates of executions and events. -/\ndef preds : Array String :=\n    {}\n", names(&doc.md.names)).unwrap();
    writeln!(o, "/-- The memory-model phrase rows. -/\ndef phrases : Array MPhrase :=\n    {phrases}\n").unwrap();
    writeln!(o, "/-- The memory model's tables. -/\ndef mdecls : MemDecls := {{ rels := rels, preds := preds, phrases := phrases }}\n").unwrap();
    for (_, src) in &last {
        writeln!(o, "{src}").unwrap();
    }
    writeln!(o, "/-- Section 29, from `<emu-clause id=\"sec-memory-model\">` to its close. -/\ndef blocks : List Block := {top}\n").unwrap();
    writeln!(o, "end Ecma.Gen.Memory").unwrap();
    files.push(("Memory".into(), o));
    let mut total = 0;
    for (m, src) in &files {
        total += src.len();
        std::fs::write(dir.join(format!("{m}.lean")), src).map_err(|e| e.to_string())?;
    }
    Ok(format!(
        "section 29: {} sentences ({} informative prose, channel (c)), {} field rows, {} clauses; {} modules, {} bytes",
        em.sents,
        em.prose,
        em.rows,
        em.defs.len(),
        files.len(),
        total
    ))
}
