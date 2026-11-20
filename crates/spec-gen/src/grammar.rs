//! The step grammar: built-in productions (precedence, lists, the type
//! lexicon) and phrase templates, each with the tier that added it.

use crate::engine::{kind_ok, mk, open_to, Cat, El, Item, Kc, Node, Op, Parser, Rid, Rule};
use crate::token::{Tok, K};
use std::collections::HashMap;
use std::rc::Rc;

pub type Out = Vec<(usize, Rc<Node>)>;

fn is_p(t: &Tok, v: &str) -> bool {
    t.k == K::Punct && t.v == v
}

fn is_w(t: &Tok, v: &str) -> bool {
    t.k == K::Word && t.v == v
}

fn n(nd: &Rc<Node>) -> Item {
    Item::N(nd.clone(), false)
}

fn l(s: &str) -> Item {
    Item::L(s.to_string(), false)
}

/// The best tree per end of a round's new candidates.
fn dedup(p: &Parser, v: Out) -> Out {
    p.select(v)
}

fn b_e(p: &mut Parser, i: usize) -> Out {
    let mut res = infix(p, i, "Prod", &["+", "-"], &["plus"], Op::Add);
    let mut new = Vec::new();
    for (j, nd) in &res {
        let j = *j;
        if j + 1 < p.n && is_w(&p.t[j], "occurrences") && is_w(&p.t[j + 1], "of") && !(p.munch && open_to(p.g, nd, Op::Add)) {
            for (k, a) in p.cat("A", j + 2).iter() {
                new.push((*k, mk(Rid::B("occurrences"), "occurrences", vec![n(nd), l("occurrences"), l("of"), n(a)], i, *k)));
            }
        }
    }
    // `a if c and b if d`: a value by two cases
    for (j, nd) in res.clone() {
        if j >= p.n || !is_w(&p.t[j], "if") {
            continue;
        }
        for (k, c1) in p.cat("C", j + 1).iter() {
            if *k >= p.n || !is_w(&p.t[*k], "and") {
                continue;
            }
            for (m, e2) in p.cat("Prod", k + 1).iter() {
                if *m >= p.n || !is_w(&p.t[*m], "if") {
                    continue;
                }
                for (q, c2) in p.cat("C", m + 1).iter() {
                    new.push((*q, mk(Rid::B("if-and-if"), "if-and-if", vec![n(&nd), l("if"), n(c1), l("and"), n(e2), l("if"), n(c2)], i, *q)));
                }
            }
        }
    }
    let new = dedup(p, new);
    res.extend(new);
    res
}

fn b_prod(p: &mut Parser, i: usize) -> Out {
    infix(p, i, "A", &["×", "/"], &["modulo", "times"], Op::Mul)
}

fn infix(p: &mut Parser, i: usize, sub: Cat, puncts: &[&str], words: &[&str], op: Op) -> Out {
    let mut res: Out = p.cat(sub, i).to_vec();
    let mut frontier = res.clone();
    while !frontier.is_empty() {
        let mut new = Vec::new();
        for (j, nd) in &frontier {
            let j = *j;
            if j >= p.n {
                continue;
            }
            let t = &p.t[j];
            if !((t.k == K::Punct && puncts.contains(&t.v.as_str())) || (t.k == K::Word && words.contains(&t.v.as_str()))) {
                continue;
            }
            if p.munch && open_to(p.g, nd, op) {
                continue;
            }
            let v = t.v.clone();
            let name: &'static str = Box::leak(format!("arith:{v}").into_boxed_str());
            for (k, nd2) in p.cat(sub, j + 1).iter() {
                new.push((*k, mk(Rid::B(name), name, vec![n(nd), l(&v), n(nd2)], i, *k)));
            }
        }
        let new = dedup(p, new);
        res.extend(new.iter().cloned());
        frontier = new;
    }
    res
}

fn b_a(p: &mut Parser, i: usize) -> Out {
    let mut res = Vec::new();
    if i < p.n {
        let t = p.t[i].clone();
        if t.k == K::Punct && (t.v == "?" || t.v == "!" || t.v == "-" || t.v == "+") {
            let glue = t.v == "-" || t.v == "+";
            let name: &'static str = Box::leak(format!("unary:{}", t.v).into_boxed_str());
            for (j, nd) in p.cat("A", i + 1).iter() {
                res.push((*j, mk(Rid::B(name), name, vec![l(&t.v), Item::N(nd.clone(), glue)], i, *j)));
            }
        }
    }
    res.extend(p.cat("Post", i).iter().cloned());
    res
}

fn b_post(p: &mut Parser, i: usize) -> Out {
    let mut res: Out = p.cat("P", i).to_vec();
    let mut frontier = res.clone();
    let mut rounds = 0;
    while !frontier.is_empty() && rounds < 8 {
        rounds += 1;
        let mut new = Vec::new();
        for (j, nd) in &frontier {
            let j = *j;
            if j >= p.n {
                continue;
            }
            if p.munch && open_to(p.g, nd, Op::Post) {
                continue;
            }
            let t = p.t[j].clone();
            let tk = |k: usize| Item::T(k, true);
            if is_p(&t, ".") && j + 1 < p.n && p.t[j + 1].k == K::Field {
                new.push((j + 2, mk(Rid::B("field"), "field", vec![n(nd), Item::L(".".into(), true), tk(j + 1)], i, j + 2)));
            } else if is_p(&t, ".")
                && j + 2 < p.n
                && p.t[j + 1].k == K::Word
                && p.t[j + 1].v.starts_with(|c: char| c.is_uppercase())
                && is_p(&p.t[j + 2], "(")
            {
                for (k, an) in p.cat("ArgsP", j + 2).iter() {
                    new.push((
                        *k,
                        mk(Rid::B("mcall"), "mcall", vec![n(nd), Item::L(".".into(), true), tk(j + 1), Item::N(an.clone(), true)], i, *k),
                    ));
                }
            } else if is_p(&t, "(") && j + 4 < p.n && is_w(&p.t[j + 1], "that") && is_w(&p.t[j + 2], "is") && is_p(&p.t[j + 3], ",") {
                // `64 (that is, 8<sup>2</sup>)`: the value written another way
                for (k, ex) in p.cat("E", j + 4).iter() {
                    if *k < p.n && is_p(&p.t[*k], ")") {
                        let items = vec![n(nd), l("("), Item::L("that".into(), true), l("is"), Item::L(",".into(), true), n(ex), Item::L(")".into(), true)];
                        new.push((k + 1, mk(Rid::B("that-is"), "that-is", items, i, k + 1)));
                    }
                }
            } else if is_p(&t, "(") && matches!(nd.name, "field" | "var" | "paren" | "meta") {
                for (k, an) in p.cat("ArgsP", j).iter() {
                    new.push((*k, mk(Rid::B("apply"), "apply", vec![n(nd), Item::N(an.clone(), true)], i, *k)));
                }
            } else if is_p(&t, "[") {
                for (k, ix) in p.cat("E", j + 1).iter() {
                    if *k < p.n && is_p(&p.t[*k], "]") {
                        new.push((
                            k + 1,
                            mk(
                                Rid::B("index"),
                                "index",
                                vec![n(nd), Item::L("[".into(), true), Item::N(ix.clone(), true), Item::L("]".into(), true)],
                                i,
                                k + 1,
                            ),
                        ));
                    }
                }
            } else if t.k == K::SupO && p.maxtier >= 2 {
                for (k, ex) in p.cat("E", j + 1).iter() {
                    if *k < p.n && p.t[*k].k == K::SupC {
                        new.push((k + 1, mk(Rid::B("pow"), "pow", vec![n(nd), tk(j), Item::N(ex.clone(), true), tk(*k)], i, k + 1)));
                    }
                }
            } else if t.k == K::Poss && p.maxtier >= 2 {
                let mut k = j + 1;
                let mut items = vec![n(nd), Item::L("'s".into(), true)];
                while k < p.n && p.t[k].k == K::Word && p.t[k].v.starts_with(|c: char| c.is_uppercase()) && items.len() < 5 {
                    items.push(Item::T(k, false));
                    k += 1;
                    new.push((k, mk(Rid::B("poss"), "poss", items.clone(), i, k)));
                }
            }
        }
        let new = dedup(p, new);
        res.extend(new.iter().cloned());
        frontier = new;
    }
    res
}

fn b_c(p: &mut Parser, i: usize) -> Out {
    conn(p, i, "CA", false, false)
}

/// Whether a chain's connectives close every run of bare commas with `, and` / `, or`.
fn closed_list(nd: &Node) -> bool {
    let mut kinds = Vec::new();
    let mut cur = nd;
    while cur.name.starts_with("cond:") {
        kinds.push(match &cur.items[1..cur.items.len() - 1] {
            [Item::L(c, _)] if c == "," => 0,
            [_] => 1,
            _ => 2,
        });
        let Item::N(first, _) = &cur.items[0] else { break };
        cur = first;
    }
    let mut pending = false;
    for k in kinds.iter().rev() {
        match k {
            0 => pending = true,
            1 if pending => return false,
            _ => pending = false,
        }
    }
    !pending
}

/// Atoms of `atom` joined by `and`, `or`, `,`, `, and`, `, or`; with `munch`,
/// never after an atom whose right edge is a hole that takes the connective;
/// with `closed`, only chains whose bare commas a `, and` / `, or` closes.
pub fn conn(p: &mut Parser, i: usize, atom: Cat, munch: bool, closed: bool) -> Out {
    let mut res: Out = p.cat(atom, i).to_vec();
    let mut frontier = res.clone();
    let mut rounds = 0;
    while !frontier.is_empty() && rounds < 6 {
        rounds += 1;
        let mut new = Vec::new();
        for (j, nd) in &frontier {
            let j = *j;
            if j >= p.n || (munch && open_to(p.g, nd, Op::Conn)) {
                continue;
            }
            if p.munch && open_to(p.g, nd, Op::Conj) {
                continue;
            }
            let t = &p.t[j];
            let (conn, k): (Vec<String>, usize) =
                if is_p(t, ",") && j + 1 < p.n && p.t[j + 1].k == K::Word && (p.t[j + 1].v == "and" || p.t[j + 1].v == "or") {
                    (vec![",".into(), p.t[j + 1].v.clone()], j + 2)
                } else if t.k == K::Word && (t.v == "and" || t.v == "or") {
                    (vec![t.v.clone()], j + 1)
                } else if is_p(t, ",") {
                    (vec![",".into()], j + 1)
                } else {
                    continue;
                };
            let name: &'static str = Box::leak(format!("cond:{}", conn.last().unwrap()).into_boxed_str());
            for (k2, nd2) in p.cat(atom, k).iter() {
                let mut items = vec![n(nd)];
                items.extend(conn.iter().map(|c| l(c)));
                items.push(n(nd2));
                new.push((*k2, mk(Rid::B(name), name, items, i, *k2)));
            }
        }
        let new = dedup(p, new);
        res.extend(new.iter().filter(|(_, nd)| !closed || closed_list(nd)).cloned());
        frontier = new;
    }
    // `c1, or if c2` and `c1 if and only if c2`: the loosest connectives, right-nested
    let mut outer = Vec::new();
    for (j, nd) in &res {
        let j = *j;
        if p.munch && open_to(p.g, nd, Op::Conj) {
            continue;
        }
        for (name, words) in OUTER_CONNS {
            let k = j + words.len();
            if k < p.n && words.iter().enumerate().all(|(x, w)| p.t[j + x].v == *w && matches!(p.t[j + x].k, K::Word | K::Punct)) {
                for (e, nd2) in p.cat("C", k).iter() {
                    let mut items = vec![n(nd)];
                    items.extend(words.iter().map(|w| l(w)));
                    items.push(n(nd2));
                    outer.push((*e, mk(Rid::B(name), name, items, i, *e)));
                }
            }
        }
    }
    let outer = dedup(p, outer);
    res.extend(outer);
    res
}

/// The connectives that join whole conditions: the node name and its words.
pub const OUTER_CONNS: &[(&str, &[&str])] = &[("cond-orif", &[",", "or", "if"]), ("cond-iff", &["if", "and", "only", "if"])];

/// `item (, item)*`; or, with `english`, an English list: `a and b`, `a, b, and c`, `a or b`.
fn list(p: &mut Parser, i: usize, item: Cat, english: bool) -> Out {
    list_of(p, i, item, english, &["and", "or"], false)
}

/// `list`, the English form joined only by the words `conjs`; with `comma2`,
/// also `a, or b` (a two-item list whose first item ends in a nested list).
pub fn list_of(p: &mut Parser, i: usize, item: Cat, english: bool, conjs: &[&str], comma2: bool) -> Out {
    let firsts: Out = p.cat(item, i).to_vec();
    if !english {
        let mut res: Out = firsts.iter().map(|(j, nd)| (*j, mk(Rid::B("list"), "list", vec![n(nd)], i, *j))).collect();
        let mut frontier = res.clone();
        while !frontier.is_empty() {
            let mut new = Vec::new();
            for (j, nd) in &frontier {
                if *j < p.n && is_p(&p.t[*j], ",") {
                    for (k, nd2) in p.cat(item, j + 1).iter() {
                        let mut items = nd.items.clone();
                        items.push(l(","));
                        items.push(n(nd2));
                        new.push((*k, mk(Rid::B("list"), "list", items, i, *k)));
                    }
                }
            }
            let new = dedup(p, new);
            res.extend(new.iter().cloned());
            frontier = new;
        }
        return res;
    }
    let mut out = Vec::new();
    let mut frontier: Vec<(Vec<Item>, usize)> = firsts.iter().map(|(j, nd)| (vec![n(nd)], *j)).collect();
    let mut count = 1;
    while !frontier.is_empty() && count < 12 {
        let mut new: Vec<(Vec<Item>, usize)> = Vec::new();
        for (tr, j) in &frontier {
            let j = *j;
            if j >= p.n {
                continue;
            }
            let t = p.t[j].clone();
            if t.k == K::Word && conjs.contains(&t.v.as_str()) && count == 1 {
                for (k, nd2) in p.cat(item, j + 1).iter() {
                    let mut items = tr.clone();
                    items.push(l(&t.v));
                    items.push(n(nd2));
                    out.push((*k, mk(Rid::B("elist"), "elist", items, i, *k)));
                }
            }
            if is_p(&t, ",") {
                if j + 1 < p.n && p.t[j + 1].k == K::Word && conjs.contains(&p.t[j + 1].v.as_str()) && (count >= 2 || comma2) {
                    let w = p.t[j + 1].v.clone();
                    for (k, nd2) in p.cat(item, j + 2).iter() {
                        let mut items = tr.clone();
                        items.push(l(","));
                        items.push(l(&w));
                        items.push(n(nd2));
                        out.push((*k, mk(Rid::B("elist"), "elist", items, i, *k)));
                    }
                }
                for (k, nd2) in p.cat(item, j + 1).iter() {
                    let mut items = tr.clone();
                    items.push(l(","));
                    items.push(n(nd2));
                    new.push((items, *k));
                }
            }
        }
        // one partial list per end: the candidates with the same end share their prefix's reading
        let mut seen: HashMap<usize, (Vec<Item>, usize)> = HashMap::new();
        for (tr, k) in new {
            seen.entry(k).or_insert((tr, k));
        }
        let mut v: Vec<_> = seen.into_values().collect();
        v.sort_by_key(|x| x.1);
        frontier = v;
        count += 1;
    }
    out
}

fn b_args(p: &mut Parser, i: usize) -> Out {
    list(p, i, "E", false)
}

fn b_el(p: &mut Parser, i: usize) -> Out {
    let mut res: Out = p.cat("E", i).iter().map(|(j, nd)| (*j, mk(Rid::B("elist1"), "elist1", vec![n(nd)], i, *j))).collect();
    res.extend(list(p, i, "E", true));
    res
}

/// Value alternatives: `a or b`, `a, b, or c`.
fn b_alt(p: &mut Parser, i: usize) -> Out {
    list_of(p, i, "E", true, &["or"], false)
}

fn b_field_inits(p: &mut Parser, i: usize) -> Out {
    list(p, i, "FI", false)
}

fn b_field_names(p: &mut Parser, i: usize) -> Out {
    list(p, i, "FN", false)
}

fn b_cun(p: &mut Parser, i: usize) -> Out {
    if i + 2 < p.n && p.t[i].k == K::Num && (p.t[i].v.starts_with("0x") || p.t[i].v.starts_with("U+")) && is_p(&p.t[i + 1], "(") {
        let mut k = i + 2;
        let mut ws = Vec::new();
        while k < p.n
            && p.t[k].k == K::Word
            && (is_upper(&p.t[k].v.replace('-', "")) || p.t[k].v.chars().all(|c| c.is_ascii_digit()))
        {
            ws.push(k);
            k += 1;
        }
        while k < p.n && p.t[k].k == K::Num && !ws.is_empty() {
            ws.push(k);
            k += 1;
        }
        if !ws.is_empty() && k < p.n && is_p(&p.t[k], ")") {
            let mut items = vec![Item::T(i, false), l("(")];
            items.extend(ws.iter().map(|&w| Item::T(w, false)));
            items.push(l(")"));
            return vec![(k + 1, mk(Rid::B("cuname"), "cuname", items, i, k + 1))];
        }
    }
    vec![]
}

fn is_upper(s: &str) -> bool {
    s.chars().any(|c| c.is_alphabetic()) && !s.chars().any(|c| c.is_lowercase())
}

fn b_prose(p: &mut Parser, i: usize) -> Out {
    if i < p.n {
        vec![(p.n, mk(Rid::B("prose"), "prose", vec![Item::P(i, p.n, false)], i, p.n))]
    } else {
        vec![]
    }
}

/// The type lexicon: the spec's own type vocabulary (`~` joins words).
const TYPES: &str = "
String Number BigInt Symbol Boolean Object List Record Set Relation Undefined Null
integer integral~Number non-negative~integer positive~integer negative~integer
normal~completion abrupt~completion throw~completion return~completion break~completion continue~completion
Completion~Record MatchState MatcherContinuation Matcher Abstract~Closure Job~Abstract~Closure
Parse~Node Private~Name CharSet CharSetElement Data~Block Shared~Data~Block property~key array~index integer~index
ECMAScript~language~value language~value mathematical~value extended~mathematical~value code~unit code~point Unicode~code~point
execution~context ECMAScript~code~execution~context Property~Descriptor PropertyDescriptor data~property accessor~property
nonterminal production character Parse~Node PrivateElement ClassElementName Job function~object constructor
ReadSharedMemory WriteSharedMemory ReadModifyWriteSharedMemory Shared~Data~Block~event
read-modify-write~modification~function JobCallback Agent~Record agent~signifier
sequence~of~code~units sequence~of~code~points empty~List empty~String
error NaN binding CaptureRange Chosen~Value~Record Matcher WeakRef FinalizationRegistry WeakMap WeakSet index
TypedArray Promise Array AsyncGenerator AsyncGeneratorRequest surrogate byte Generator ArrayBuffer SharedArrayBuffer byte~value time~value TypedArray~element~type candidate~execution
ECMAScript~source~text sequence~of~Unicode~code~points sequence~of~characters grammar~symbol Uint8Array DataView internal~slot~name
property~name Unicode~property~name Unicode~property~value epoch~nanoseconds~count Memory~event
";

pub const MODS: &[&str] = &[
    "new", "odd", "non-negative", "non-zero", "positive", "negative", "non-empty", "one-element", "possibly", "empty", "finite", "extensible",
    "revoked", "growable", "fully", "populated", "strict", "newly", "created", "single", "ordinary", "callable", "built-in", "mutable",
    "immutable", "uninitialized", "leading", "trailing", "indirect", "direct",
];
pub const HEADS: &[&str] = &["Record", "object", "event", "Closure", "instance", "Instance"];

pub fn type_set() -> std::collections::HashSet<String> {
    TYPES.split_whitespace().map(|t| t.replace('~', " ")).collect()
}

fn b_tn(p: &mut Parser, i: usize) -> Out {
    let mut res = Vec::new();
    let mut j = i;
    let mut words: Vec<usize> = Vec::new();
    while j < p.n
        && p.t[j].k == K::Word
        && (!["the", "a", "an", "of", "is", "and", "or"].contains(&p.t[j].v.as_str()) || (p.t[j].v == "of" && of_prefix(p, &words)))
        && words.len() < 7
    {
        words.push(j);
        j += 1;
        let vs: Vec<&str> = words.iter().map(|&w| p.t[w].v.as_str()).collect();
        let mut k = 0;
        while k + 1 < vs.len() && MODS.contains(&vs[k]) {
            k += 1;
        }
        let core = &vs[k..];
        let phrase = core.join(" ");
        let sing = phrase.strip_suffix('s').unwrap_or(&phrase);
        let ok = p.g.types.contains(&phrase) || p.g.types.contains(sing) || HEADS.contains(&core[core.len() - 1].trim_end_matches('s'));
        if ok {
            res.push((j, mk(Rid::B("type"), "type", words.iter().map(|&w| Item::T(w, false)).collect(), i, j)));
        }
    }
    let mut out = res.clone();
    for (j, nd) in &res {
        let last = match nd.items.last() {
            Some(Item::T(w, _)) => p.t[*w].v.as_str(),
            _ => "",
        };
        if j + 1 < p.n && is_w(&p.t[*j], "of") && matches!(last, "List" | "Lists" | "Set") {
            for (k, nd2) in b_tn(p, j + 1) {
                out.push((k, mk(Rid::B("type-of"), "type-of", vec![n(nd), l("of"), n(&nd2)], i, k)));
            }
        }
    }
    p.select(out)
}

/// Whether the words so far and `of` begin a type of the lexicon (`sequence of code points`).
fn of_prefix(p: &Parser, words: &[usize]) -> bool {
    let mut pre = words.iter().map(|&w| p.t[w].v.as_str()).collect::<Vec<_>>().join(" ");
    pre.push_str(" of ");
    !words.is_empty() && p.g.types.iter().any(|t| t.starts_with(&pre))
}

fn b_preds(p: &mut Parser, i: usize) -> Out {
    let mut res: Out = p.cat("PRED", i).iter().map(|(j, nd)| (*j, mk(Rid::B("preds"), "preds", vec![n(nd)], i, *j))).collect();
    let mut frontier = res.clone();
    while !frontier.is_empty() {
        let mut new = Vec::new();
        for (j, nd) in &frontier {
            let j = *j;
            if j < p.n && p.t[j].k == K::Word && (p.t[j].v == "and" || p.t[j].v == "or") && p.maxtier >= 2 {
                let w = p.t[j].v.clone();
                for (k, nd2) in p.cat("PRED", j + 1).iter() {
                    let mut items = nd.items.clone();
                    items.push(l(&w));
                    items.push(n(nd2));
                    new.push((*k, mk(Rid::B("preds"), "preds", items, i, *k)));
                }
            }
        }
        let new = dedup(p, new);
        res.extend(new.iter().cloned());
        frontier = new;
    }
    res
}

fn b_caps(p: &mut Parser, i: usize) -> Out {
    let mut res = Vec::new();
    let mut j = i;
    let mut ws = Vec::new();
    while j < p.n && kind_ok(&p.t[j], Kc::Cap) && ws.len() < 3 {
        ws.push(Item::T(j, false));
        j += 1;
        res.push((j, mk(Rid::B("caps"), "caps", ws.clone(), i, j)));
    }
    res
}

/// A type noun, or type nouns joined by `or`.
fn b_tnu(p: &mut Parser, i: usize) -> Out {
    let mut res: Out = p.cat("TN", i).to_vec();
    res.extend(list_of(p, i, "TN", true, &["or"], false));
    res
}

fn b_talt(p: &mut Parser, i: usize) -> Out {
    list_of(p, i, "T", true, &["or"], false)
}

fn b_field_el(p: &mut Parser, i: usize) -> Out {
    list(p, i, "FN", true)
}

fn b_htalt(p: &mut Parser, i: usize) -> Out {
    list_of(p, i, "HT1", true, &["or"], true)
}

fn b_hfl(p: &mut Parser, i: usize) -> Out {
    let mut res: Out = p.cat("HF", i).iter().map(|(j, nd)| (*j, mk(Rid::B("elist1"), "elist1", vec![n(nd)], i, *j))).collect();
    res.extend(list(p, i, "HF", true));
    res
}

pub type Builtin = fn(&mut Parser, usize) -> Out;

pub fn builtin(c: Cat) -> Option<Builtin> {
    Some(match c {
        "E" => b_e,
        "Prod" => b_prod,
        "A" => b_a,
        "Post" => b_post,
        "C" => b_c,
        "Args" => b_args,
        "EL" => b_el,
        "ALT" => b_alt,
        "FieldInits" => b_field_inits,
        "FieldNames" => b_field_names,
        "CUN" => b_cun,
        "Prose" => b_prose,
        "TN" => b_tn,
        "PREDS" => b_preds,
        "CAPS" => b_caps,
        "TALT" => b_talt,
        "TNU" => b_tnu,
        "FieldEL" => b_field_el,
        "HTALT" => b_htalt,
        "HFL" => b_hfl,
        "DFN" => crate::memmodel::b_dfn,
        "MC" => crate::memmodel::b_mc,
        "MSORTS" => crate::memmodel::b_msorts,
        _ => return None,
    })
}

/// (category, name, template, tier, synonym of)
pub type R = (Cat, &'static str, &'static str, u8, Option<&'static str>);

/// The phrases the parser builds outside `RULES` (category, name, template), which an overlay
/// entry may claim by `rule=` as it claims a rule.
pub const PARSER_FORMS: &[(&str, &str, &str)] = &[("P", "occurrences", "{E} occurrences of {E}"), ("P", "if-and-if", "{E} if {C} and {E} if {C}"), ("CA", "iff", "{C} if and only if {C}"),
    ("P", "iter-backwards", "{E} , iterating backwards from its second-to-last element"),
    ("P", "see-xref", "{E} '(' see $XREF ')'"),
    ("P", "that-is", "{E} '(' that is , {E} ')'"),
    ("P", "assoc-table", "the ( abstract operation | sequence of Unicode code points ) associated with {E} in the following table :"),
    ("PRED", "contains-such-binds", "contains ( a | an ) {TN} {V} such that {C}"),
];

pub const RULES: &[R] = &[
    // tier 1: the imperative core
    ("Step", "let", "Let {V} be {E} .", 1, None),
    ("Step", "set", "Set {E} to {E} .", 1, None),
    ("Step", "return", "Return {E} .", 1, None),
    ("Step", "return-unit", "Return .", 1, None),
    ("Step", "perform", "Perform {E} .", 1, None),
    ("Step", "if-then", "If {C} , then", 1, None),
    ("Step", "if-inline", "If {C} , {SI}", 1, None),
    ("Step", "elseif-then", "Else if {C} , then", 1, None),
    ("Step", "elseif-inline", "Else if {C} , {SI}", 1, None),
    ("Step", "else", "Else ,", 1, None),
    ("Step", "else-inline", "Else , {SI}", 1, None),
    ("Step", "assert", "Assert : {C} .", 1, None),
    ("Step", "throw", "Throw ( a | an ) $VAL exception .", 1, None),
    ("Step", "note", "NOTE : {Prose}", 1, None),
    ("Step", "repeat", "Repeat ,", 1, None),
    ("Step", "repeat-while", "Repeat , while {C} ,", 1, None),
    ("Step", "foreach", "For each element {V} of {E} , do", 1, None),
    ("Step", "append", "Append {E} to {E} .", 1, None),
    ("Step", "macro", "$CAP ^{ArgsP} .", 1, None),
    ("V", "var", "$VAR", 1, None),
    ("AV", "var", "$VAR", 1, None),
    ("P", "var", "$VAR", 1, None),
    ("P", "val", "$VAL", 1, None),
    ("P", "enum", "$ENUM", 1, None),
    ("P", "intrinsic", "$INTR", 1, None),
    ("P", "num", "$NUM", 1, None),
    ("P", "nonterminal", "$NT", 1, None),
    ("P", "field-name", "$FIELD", 1, None),
    ("P", "xref", "$XREF", 1, None),
    ("P", "call", "$WORD ^{ArgsP}", 1, None),
    ("P", "call-num", "( 𝔽 | ℝ | ℤ ) ^{ArgsP}", 1, None),
    ("P", "paren", "'(' {E} ')'", 1, None),
    ("P", "list-lit", "« [ {Args} ] »", 1, None),
    ("P", "meta", "$METAO ^{E} ^$METAC", 1, None),
    ("ArgsP", "args", "'(' [ {Args} ] ')'", 1, None),
    ("CA", "pred", "{E} {PREDS}", 1, None),
    ("CA", "rel", "{E} ( '<' | ≤ | '>' | ≥ | = | ≠ ) {E}", 1, None),
    ("CA", "paren", "'(' {C} ')'", 1, None),
    ("PRED", "is", "is {E}", 1, None),
    ("PRED", "is-not", "is not {E}", 1, None),
    ("PRED", "is-type", "is {T}", 1, None),
    ("PRED", "is-not-type", "is not {T}", 1, None),
    ("PRED", "present", "is present", 1, None),
    ("PRED", "not-present", "is not present", 1, None),
    ("PRED", "either", "is either {ALT}", 1, None),
    ("PRED", "is-alt", "is {ALT}", 1, None),
    ("T", "a", "( a | an ) {TN}", 1, None),
    // tier 2: the spec's own operators
    ("P", "this", "the $VAL=this value", 2, None),
    ("P", "new-list", "a new empty List", 2, None),
    ("P", "sdo", "[ the ] $CAP of {A}", 2, None),
    ("P", "sdo-early", "Early Errors of {A}", 2, None),
    ("P", "sdo-arg", "[ the ] $CAP of {A} with argument {E}", 2, None),
    ("P", "sdo-args", "[ the ] $CAP of {A} with arguments {EL}", 2, None),
    ("P", "numel", "the number of elements in {A}", 2, None),
    ("P", "numel-of", "the number of elements of {A}", 2, None),
    ("P", "length", "the length of {A}", 2, None),
    ("P", "listcat", "the list-concatenation of {EL}", 2, None),
    ("P", "strcat", "the string-concatenation of {EL}", 2, None),
    ("P", "substring", "the substring of {A} from {E} [ to {E} ]", 2, None),
    ("P", "rec", "[ the ] [ {TN} ] '{' {FieldInits} '}'", 2, None),
    ("P", "rec-empty", "[ the ] [ {TN} ] '{' '}'", 2, None),
    ("FI", "fi", "$FIELD ^: {E}", 2, None),
    ("P", "running-ctx", "the running execution context", 2, None),
    ("P", "current-realm", "the current Realm Record", 2, None),
    ("P", "active-fn", "the active function object", 2, None),
    ("P", "agent-record", "the Agent Record of the surrounding agent", 2, None),
    ("P", "agent-record-poss", "the surrounding agent 's Agent Record", 2, None),
    ("P", "empty-string", "the empty String", 2, None),
    ("P", "elem", "the ( sole | first | last ) element of {A}", 2, None),
    ("P", "number-for", "the Number value for {A}", 2, None),
    ("P", "bigint-for", "the BigInt value for {A}", 2, None),
    ("P", "source-text", "the source text matched by {A}", 2, None),
    ("P", "new-error", "a newly created $VAL object", 2, None),
    ("P", "covered", "the $NT that is covered by {A}", 2, None),
    ("P", "processed-as", "the $NT that {A} is processed as", 2, None),
    ("P", "list-sole", "a List whose sole element is {E}", 2, None),
    ("P", "list-elems", "a List whose elements are {EL}", 2, None),
    ("P", "copy", "a copy of {A}", 2, None),
    ("P", "code-unit", "the code unit {CUN}", 2, None),
    ("P", "code-point", "the [ single ] code point ( {CUN} | $VAR )", 2, None),
    ("P", "cuname", "{CUN}", 2, None),
    ("P", "inf", "∞", 2, None),
    ("P", "math-value", "the mathematical value of {A}", 2, None),
    ("P", "result-of", "the result of {E}", 2, None),
    ("Step", "remove", "Remove {E} from {E} .", 2, None),
    ("Step", "remove-first", "Remove the first element from {E} .", 2, None),
    ("Step", "remove-last", "Remove the last element of {E} .", 2, None),
    ("Step", "insert-first", "Insert {E} as the first element of {E} .", 2, None),
    ("Step", "prepend", "Prepend {E} to {E} .", 2, None),
    ("Step", "throw-value", "Throw {E} .", 2, None),
    ("Step", "push-ctx", "Push {E} onto the execution context stack ; {E} is now the running execution context .", 2, None),
    ("Step", "suspend", "Suspend {E} .", 2, None),
    ("Step", "suspend-remove", "Suspend {E} and remove it from the execution context stack .", 2, None),
    (
        "Step",
        "remove-ctx-restore",
        "Remove {E} from the execution context stack and restore {E} as the running execution context .",
        2,
        None,
    ),
    (
        "Step",
        "remove-ctx-restore-top",
        "Remove {E} from the execution context stack and restore the execution context that is at the top of the execution context stack as the running execution context .",
        2,
        None,
    ),
    ("Step", "remove-ctx", "Remove {E} from the execution context stack .", 2, None),
    (
        "Step",
        "resume-top",
        "Resume the context that is now on the top of the execution context stack as the running execution context .",
        2,
        None,
    ),
    ("Step", "resume-passing", "Resume {E} , passing {E} .", 2, None),
    ("PRED", "empty", "is empty", 2, None),
    ("PRED", "empty-list", "is an empty List", 2, None),
    ("PRED", "not-empty", "is not empty", 2, None),
    ("PRED", "contains", "contains {E}", 2, None),
    ("PRED", "not-contains", "does not contain {E}", 2, None),
    ("PRED", "has-slot", "has ( a | an ) $FIELD internal slot", 2, None),
    ("PRED", "not-has-slot", "does not have ( a | an ) ( $FIELD | $VAR ) internal slot", 2, None),
    ("PRED", "has-field", "has ( a | an ) $FIELD field", 2, None),
    ("PRED", "not-has-field", "does not have ( a | an ) $FIELD field", 2, None),
    ("PRED", "finite", "is finite", 2, None),
    ("PRED", "not-finite", "is not finite", 2, None),
    ("PRED", "neither", "is neither {E} nor {E}", 2, None),
    ("PRED", "one-of", "is one of {ALT}", 2, None),
    ("PRED", "not-one-of", "is not one of {ALT}", 2, None),
    ("CA", "rel3", "{E} ( '<' | ≤ ) {E} ( '<' | ≤ ) {E}", 2, None),
    ("PRED", "interval", "is in the inclusive interval from {E} to {E}", 2, None),
    // tier 3: closures, typed loops, the type language
    (
        "CLO",
        "closure",
        "a new {TN} with ( no parameters | parameters {ArgsP} ) that captures ( nothing | {EL} ) and performs the following steps when called :",
        3,
        None,
    ),
    ("Step", "let-closure", "Let {V} be {CLO}", 3, None),
    ("Step", "foreach-typed", "For each {TNU} {V} of {E} , do", 3, None),
    ("Step", "foreach-rev", "For each element {V} of {E} , in reverse List order , do", 3, None),
    ("Step", "foreach-typed-rev", "For each {TN} {V} of {E} , in reverse List order , do", 3, None),
    ("Step", "foreach-int", "For each integer {V} such that {C} , in ( ascending | descending ) order , do", 3, None),
    ("Step", "foreach-recpat", "For each Record '{' {FieldNames} '}' {V} of {E} , do", 3, None),
    ("FN", "fn", "$FIELD", 3, None),
    ("Step", "repeat-until", "Repeat , until {C} ,", 3, None),
    ("Step", "repeat-times", "Repeat {E} times :", 3, None),
    ("P", "list-of-length", "a List of length {E} whose elements are {E}", 3, None),
    ("P", "new-data-block", "a new Data Block value consisting of {E} bytes", 3, None),
    ("T", "a-list-of", "( a | an ) List of {TN}", 3, None),
    ("PRED", "is-type-or", "is {T} or {T}", 3, None),
    ("PRED", "is-type-either", "is either {T} or {T}", 3, Some("either-types")),
    ("PRED", "not-type-nor", "is neither {T} nor {T}", 3, None),
    // tier 4: long tail, iteration 1
    ("P", "this-bare", "$VAL=this value", 4, None),
    ("P", "newtarget", "NewTarget", 4, None),
    ("P", "code", "$CODE", 4, None),
    ("P", "grammar-lit", "$GRAM", 4, None),
    (
        "P",
        "constant",
        "( HoursPerDay | MinutesPerHour | SecondsPerMinute | MillisecondsPerSecond | MillisecondsPerMinute | MillisecondsPerHour | MillisecondsPerDay | NanosecondsPerDay | NanosecondsPerSecond | NanosecondsPerMillisecond | NanosecondsPerMicrosecond | MaxEpochNanoseconds | MinEpochNanoseconds )",
        4,
        None,
    ),
    ("P", "this-nt-node", "this $NT", 4, None),
    ("P", "this-parse-node", "this Parse Node", 4, None),
    ("PRED", "is-single-cp", "is the single code point {CUN}", 4, None),
    ("P", "the-nt", "the ( first | second | third | derived | | fourth ) $NT", 4, None),
    ("P", "nt-of", "the $NT of {A}", 4, None),
    ("P", "grammar-symbol", "the grammar symbol $NT", 4, None),
    ("P", "contains-infix", "{CS} Contains {A}", 4, None),
    ("CS", "cs-nt", "$NT", 4, None),
    ("CS", "cs-var", "$VAR", 4, None),
    ("CS", "cs-the", "the ( first | second | third | derived | | fourth ) $NT", 4, None),
    ("P", "numeric-value-defined", "the NumericValue of {A} as defined in $XREF", 4, None),
    ("P", "sv-defined", "the SV of {A} as defined in $XREF", 4, None),
    ("P", "tv-defined", "the TV of {A} as defined in $XREF", 4, None),
    ("P", "new-thing", "a new {TN}", 4, None),
    ("P", "select-whose", "the {TN} of {A} whose $FIELD is {E}", 4, None),
    ("P", "table-lookup-key", "the {CAPS} value specified in $XREF for {CAPS} {A}", 4, None),
    ("P", "table-lookup-row", "the {CAPS} value specified in $XREF for {A}", 4, None),
    ("P", "table-step", "the value that {E} corresponds to in $XREF", 6, None),
    ("P", "attr-of", "the value of {A} 's $FIELD attribute", 4, None),
    ("P", "cu-at", "the code unit at index {E} within {A}", 4, None),
    ("P", "cp-matched", "the code point matched by {A}", 4, None),
    ("P", "numeric-value", "the numeric value of {A}", 4, None),
    ("P", "time-now", "the time value '(' UTC ')' identifying the current time", 4, None),
    ("P", "clamp", "the result of clamping {E} between {E} and {E}", 4, None),
    ("P", "union", "the union of [ CharSets ] {EL}", 4, None),
    ("P", "char-whose", "the character whose character value is {E}", 4, None),
    ("P", "number-corresponds", "the ( Number | BigInt ) value that corresponds to {A}", 4, None),
    ("P", "component", "the $CAP component of {A}", 4, None),
    (
        "P",
        "bitwise",
        "the result of applying the ( bitwise | single-bit ) $TAG=<code> ^ ( AND ^ $TAG=</code> | XOR ^ $TAG=</code> '(' exclusive OR ')' | OR ^ $TAG=</code> '(' inclusive OR ')' ) operation to {E} and {E}",
        4,
        None,
    ),
    ("P", "number-of", "the number of ( elements | code units | code points | bytes ) in {A}", 4, Some("numel")),
    ("P", "binding-for", "the binding for {E} in {E}", 4, None),
    ("P", "bound-value", "the value currently bound to {E} in {E}", 4, None),
    ("P", "instance-of-prod", "an instance of the production $GRAM", 4, None),
    ("P", "strcat-colon", "the string-concatenation of :", 4, None),
    (
        "CLO",
        "closure-atomic",
        "a new {TN} with ( no parameters | parameters {ArgsP} ) that captures ( nothing | {EL} ) and performs the following steps atomically when called :",
        4,
        None,
    ),
    ("Step", "return-closure", "Return {CLO}", 4, None),
    ("Step", "set-as-specified", "Set {E} as specified in $XREF .", 4, None),
    ("Step", "set-definition", "Set {E} to the definition specified in $XREF .", 4, None),
    ("Step", "if-else-inline", "If {C} , {SIn} ; else {SI}", 4, None),
    ("Step", "foreach-nt", "For each $NT {V} of {E} , do", 4, None),
    ("Step", "foreach-child", "For each child node {V} of this Parse Node , do", 4, None),
    ("Step", "foreach-child-of", "For each child node {V} of {E} , do", 4, None),
    (
        "Step",
        "foreach-own-key",
        "For each own property key {V} of {E} such that {C} , in ( ascending numeric index order | ascending chronological order of property creation | descending numeric index order ) , do",
        4,
        None,
    ),
    ("Step", "assert-if", "Assert : If {C} , then {C} .", 4, None),
    ("Step", "unreachable", "Assert : This step is never reached .", 4, None),
    ("Step", "replace-elem", "Replace the element of {E} whose value is {E} with an element whose value is {E} .", 4, None),
    ("Step", "store-bytes", "Store the individual bytes of {E} into {E} , starting at {E} ^'[' ^{E} ^']' .", 4, None),
    (
        "Step",
        "set-eval-state",
        "Set the code evaluation state of {E} such that when evaluation is resumed for that execution context , {E} will be called with no arguments .",
        4,
        None,
    ),
    ("Step", "elseif-starts", "Else if {E} starts with {E} , then", 4, Some("elseif-then")),
    ("CA", "host-web", "the host is a web browser [ or otherwise supports $XREF ]", 4, None),
    ("CA", "in-critical", "the surrounding agent is in the critical section for {E}", 4, None),
    ("CA", "same-tn", "{E} and {E} are the same {TN}", 4, None),
    ("CA", "not-same-tn", "{E} and {E} are not the same {TN}", 4, None),
    ("PRED", "already-suspended", "is not already suspended", 4, None),
    ("PRED", "has-method", "has ( a | an ) $FIELD internal method", 4, None),
    ("PRED", "instance-of", "is an instance of {T}", 4, None),
    ("PRED", "instance-of-prod-p", "is an instance of the production $GRAM", 4, None),
    ("PRED", "has-binding-yes", "has a binding for {E}", 4, None),
    ("PRED", "has-binding-no", "does not [ already ] have a binding for {E}", 4, None),
    ("PRED", "not-yet-initialized", "has not yet been initialized", 4, None),
    ("PRED", "starts-with", "starts with {E}", 4, None),
    ("PRED", "not-include", "does not include the element {E}", 4, None),
    ("T", "a-nt", "( a | an ) $NT", 4, None),
    ("T", "a-var", "( a | an ) $VAR", 4, None),
    ("T", "a-that", "( a | an ) {TN} that {PREDS}", 4, None),
    ("T", "closure-type-none", "an Abstract Closure with no parameters", 4, None),
    // tier 5: long tail, iteration 2
    ("Step", "let-colon", "Let {V} be the string-concatenation of :", 5, None),
    ("Step", "return-colon", "Return the string-concatenation of :", 5, None),
    ("Step", "set-colon", "Set {E} to the string-concatenation of :", 5, None),
    (
        "Step",
        "let-table",
        "Let {V} be the ( abstract operation | sequence of Unicode code points ) associated with {E} in the following table :",
        5,
        None,
    ),
    ("Step", "add", "Add {E} to {E} .", 5, None),
    ("Step", "reverse", "Reverse the order of the elements of {E} .", 5, None),
    ("Step", "foreach-index", "For each index {V} of {E} , do", 5, None),
    ("Step", "foreach-such-that", "For each {TN} {V} such that {C} , do", 5, None),
    ("Step", "choose", "Choose any such {V} .", 5, None),
    (
        "Step",
        "resume-let",
        "$METAO ^Resume the suspended evaluation of {E} ^$METAC passing {E} as the result of the operation that suspended it . Let {V} be the Completion Record passed by the resumed computation .",
        5,
        None,
    ),
    ("Step", "return-see", "Return {E} '(' see $XREF ')' .", 5, None),
    ("Step", "assert-critical", "Assert : The surrounding agent is in the critical section for {E} .", 5, None),
    ("P", "surrounding-agent", "the surrounding agent", 5, None),
    ("P", "resumed-with", "the Completion Record with which {E} was just resumed", 5, None),
    ("P", "pi", "π", 5, None),
    ("P", "approx", "an implementation-approximated Number value representing {E}", 5, None),
    ("P", "impl-choice", "an implementation-defined choice of either {E} or {E}", 5, None),
    ("P", "nondet-bytes", "a List of length {E} whose elements are nondeterministically chosen byte values", 5, None),
    ("P", "nondet-byte", "a nondeterministically chosen byte value", 5, None),
    ("P", "remainder", "the remainder of dividing {E} by {E}", 5, None),
    ("P", "number-corr", "the ECMAScript Number value corresponding to {A}", 5, None),
    ("P", "ext-math-value", "the extended mathematical value of {A}", 5, None),
    ("P", "cp-whose", "the ( code point | code unit ) whose numeric value is {E}", 5, None),
    ("P", "first-cu", "the first code unit of {A}", 5, None),
    ("P", "recognized-as", "the source text that was recognized as {A}", 5, None),
    ("P", "slots-listed", "the internal slots listed in $XREF", 5, None),
    ("P", "empty-coll", "an empty ( List [ of {TN} ] | Set )", 5, None),
    ("P", "empty-seq", "the empty sequence of Unicode code points", 5, None),
    ("P", "charset-one", "a one-element CharSet containing [ the character ] {A}", 5, None),
    ("P", "charset-single", "the CharSet containing the single character {A}", 5, None),
    ("P", "charset-op", "the ( union | intersection ) of CharSets {E} and {E}", 5, None),
    ("P", "cp-list", "the List of Unicode code points {A}", 5, None),
    ("P", "character", "the character {A}", 5, None),
    ("P", "char-value", "the character value of character {A}", 5, None),
    ("P", "pd-empty", "( a new Property Descriptor that initially has no fields | a newly created Property Descriptor with no fields )", 5, None),
    ("P", "env-empty", "a new {TN} containing no bindings", 5, None),
    ("CA", "contains-cond", "{CS} Contains {A}", 5, None),
    ("CA", "stack-empty", "the execution context stack is empty", 5, None),
    ("CA", "plural-finite-numbers", "{EL} are finite Numbers", 5, None),
    ("CA", "plural-nonzero-finite-numbers", "{EL} are non-zero finite Numbers", 5, None),
    ("CA", "same-count", "{EL} have the same number of elements", 5, None),
    ("CA", "not-same-count", "{EL} do not have the same number of elements", 5, None),
    ("PRED", "either-types", "is [ not ] either {TALT}", 5, None),
    ("PRED", "has-slots", "has {FieldEL} internal slots", 5, None),
    ("PRED", "now", "is now {E}", 5, None),
    ("PRED", "parity", "is ( even | odd )", 5, None),
    ("PRED", "not-interval", "is not in the inclusive interval from {E} to {E}", 5, None),
    ("PRED", "own-prop", "has an own property with key {E}", 5, None),
    ("PRED", "not-own-prop", "does not have an own property with key {E}", 5, None),
    ("T", "a-nt-node", "( a | an ) $NT Parse Node", 5, None),
    // equation SDOs (category EQ): `The SV of <emu-grammar>…</emu-grammar> is ….`
    ("EQ", "eq", "The $CAP of {EQG} is {E} .", 1, None),
    ("EQ", "eq-where", "The $CAP of {EQG} is {E} , where {WH} .", 1, None),
    ("EQ", "eq-if", "The $CAP of {EQG} is {E} if {C} . Otherwise , it is {E} .", 1, None),
    ("EQG", "eqg-one", "$GRAM", 1, None),
    ("EQG", "eqg-more", "$GRAM or of {EQG}", 1, None),
    ("WH", "wh-one", "{V} is {E}", 1, None),
    ("WH", "wh-and", "{V} is {E} , and {WH}", 1, None),
    ("WH", "wh-and-bare", "{V} is {E} and {WH}", 6, None),
    ("P", "negative-of", "the negative of {A}", 5, None),
    ("P", "performing-utf16", "the result of performing UTF16EncodeCodePoint on {E}", 5, None),
    ("P", "string-of", "the String value ( consisting of | containing ) {EL}", 5, None),
    ("P", "cu-table", "the code unit whose numeric value is determined by {A} according to $XREF", 5, None),
    ("P", "cp-this-prod", "the single code point matched by this production", 5, None),
    ("P", "numcp-excl", "the number of code points in {A} , excluding all occurrences of $NT", 5, None),
    // the spec's grammar talk: Parse Nodes, source text, early-error conditions
    ("P", "this-production", "this ( production | phrase )", 5, None),
    ("P", "nt-containing", "the $NT containing {A}", 5, None),
    ("P", "enclosing-nt", "the enclosing $NT", 5, None),
    ("P", "goal-symbol", "the ( syntactic goal symbol | goal symbol of the syntactic grammar )", 5, None),
    ("P", "lexical-production", "the $NT lexical grammar production", 5, None),
    ("P", "some-cp-matched", "some [ Unicode ] code point matched by {A}", 5, None),
    ("P", "any-nt-except", "any $NT except for {ALT}", 5, None),
    ("PRED", "stringvalue-any-nt-except", "is the StringValue of any $NT except for {ALT}", 5, None),
    ("PRED", "stringvalue-terminal-except", "is the String value of any terminal of $NT except for {ALT}", 5, None),
    ("P", "that-source", "that source text", 5, None),
    (
        "GP",
        "grammar-param",
        "( $PARAM=Yield | $PARAM=Await | $PARAM=In | $PARAM=Return | $PARAM=Tagged | $PARAM=UnicodeMode | $PARAM=UnicodeSetsMode | $PARAM=NamedCaptureGroups )",
        5,
        None,
    ),
    ("PRED", "has-param", "has ( a | an ) {GP} parameter", 5, None),
    ("PRED", "not-has-param", "does not have ( a | an ) {GP} parameter", 5, None),
    ("CA", "param-not-set", "the {GP} parameter was not set", 5, None),
    ("PRED", "dups", "contains any duplicate ( entries | elements )", 5, None),
    ("PRED", "dups-for", "contains any duplicate entries for {E}", 5, None),
    ("CA", "two-of-form", "at least two of those entries were obtained from productions of the form $GRAM", 5, None),
    ("CA", "source-matched", "any source text is matched by {A}", 5, None),
    ("CA", "direct-eval", "the source text containing {A} is eval code that is being processed by a direct eval", 5, None),
    ("CA", "that-non-strict", "that source text is non-strict code", 5, None),
    ("CA", "source-strict", "the source text matched by {A} is strict mode code", 5, None),
    ("PRED", "gt", "is strictly greater than {E}", 5, None),
    ("PRED", "ge", "is greater than or equal to {E}", 5, None),
    ("CA", "two-distinct", "{E} contains two distinct $NT ^s {V} and {V} such that {C} and such that {C}", 5, None),
    ("PRED", "two-entries", "has two different entries {V} and {V} such that {C}", 5, None),
    ("PRED", "same-cp-twice", "contains the same code point more than once", 5, None),
    ("PRED", "more-than-once", "contains more than one occurrence of {E}", 5, None),
    ("PRED", "contains-any-nts", "contains any $NT ^s", 5, None),
    ("CA", "elem-occurs", "any element of {E} also occurs in {E}", 5, None),
    ("CA", "elem-not-occurs", "any element of {E} does not also occur in either {E} , or {E}", 5, None),
    ("CA", "cp-also-in", "any code point in {E} is also contained in {E}", 5, None),
    ("CA", "both-empty", "{EL} are both empty", 5, None),
    ("PRED", "matched-by-pos", "is matched by {E}", 5, None),
    ("PRED", "matched-by-not", "is not matched by {E}", 5, None),
    ("PRED", "not-some-cp-matched", "is not ( some | the numeric value of some ) [ Unicode ] code point matched by {A}", 6, None),
    ("PRED", "contained-within", "is contained within {T}", 5, None),
    ("T", "a-nt-that", "( a | an ) $NT that {PREDS}", 5, None),
    ("PRED", "parsed-for-json", "is being parsed for $WORD=ParseJSON", 5, None),
    ("CA", "getter-setter", "the name is used once for a getter and once for a setter and in no other entries", 5, None),
    ("CA", "both-static", "the getter and setter are either both static or both non-static", 5, None),
    (
        "PRED",
        "not-nested",
        "is not nested , directly or indirectly '(' but not crossing function or $CODE initialization block boundaries ')' , within {T}",
        5,
        None,
    ),
    (
        "PRED",
        "not-nested-alt",
        "is not nested , directly or indirectly '(' but not crossing function or $CODE initialization block boundaries ')' , within {TALT}",
        5,
        None,
    ),
    // early-error rules (category ER: the sentences of an Early Errors bullet; ERI: after `If C,`)
    ("EB", "eb-one", "{ER}", 1, None),
    ("EB", "eb-more", "{ER} {EB}", 1, None),
    ("ER", "syntax-error", "It is ( a | an early ) Syntax Error if {C} [ ( unless {C} | , unless {C} | ^$TAG , unless {C} ^$TAG ) ] .", 1, None),
    ("ERI", "syntax-error", "it is ( a | an early ) Syntax Error if {C} [ ( unless {C} | , unless {C} | ^$TAG , unless {C} ^$TAG ) ] .", 1, None),
    ("ER", "if-inline", "If {C} , {ERI}", 1, None),
    ("ER", "syntax-error-ins", "It is a Syntax Error if {C} $TAG=<ins> ^and {C} ^$TAG=</ins> .", 1, None),
    ("ER", "must-cover", "$NT must cover {T} .", 1, None),
    ("ERI", "must-cover", "$NT must cover {T} .", 1, None),
    ("ER", "rules-applied", "The Early Error rules for $GRAM are applied .", 1, None),
    ("ERI", "rules-applied", "the Early Error rules for $GRAM are applied .", 1, None),
    ("ER", "foreach-in", "For each $NT {V} in {E} : It is a Syntax Error if {C} .", 1, None),
    ("ER", "more-rules", "Additional early error rules for {E} ( in | within ) direct eval are defined in $XREF .", 1, None),
    ("ER", "not-applied", "This rule is not applied if {C} [ '(' see step $XREF of $WORD ')' ] .", 1, None),
    ("ER", "recursively-applied", "This rule is recursively applied .", 6, None),
    ("CA", "both-following", "both of the following conditions are true : {C}", 6, None),
    ("P", "extreme", "the ( largest | smallest ) {TN} {V} '(' closest to {E} ')' such that {C}", 6, None),
    ("Step", "let-such-that", "Let {VL} be integers such that {C} , choosing them so that {OBJS} .", 6, None),
    ("Step", "let-such-that-any", "Let {VL} be integers such that {C} .", 6, None),
    ("VL", "vl-two", "{V} and {V}", 6, None),
    ("VL", "vl-three", "{V} , {V} , and {V}", 6, None),
    ("OBJS", "objs-one", "{OBJ}", 6, None),
    ("OBJS", "objs-then", "{OBJ} , then so that {OBJS}", 6, None),
    ("OBJ", "obj", "{E} is as ( small | large ) as possible", 6, None),
    ("Step", "find-such-that", "Find ( a | an ) {TN} {V} such that {C} ; but if this is not possible '(' because some argument is out of range ')' , return {E} .", 6, None),
    ("CA", "alg-true", "the following algorithm returns $VAL=true : $ALG", 6, None),
    ("CA", "dup-only-functions", "the duplicate entries are only bound by FunctionDeclarations", 6, None),
    ("CA", "derives-error", "$NT ultimately derives a phrase that , if used in place of $NT , would produce a Syntax Error according to these rules", 6, None),
    // header types (category HT, not reachable from Step)
    ("HT", "ht-one", "{HT1}", 1, None),
    ("HT", "ht-alt", "{HTALT}", 1, None),
    ("HT", "ht-either", "either {HTALT}", 1, None),
    ("HT1", "ht-type", "{T}", 1, None),
    ("HT1", "ht-enum", "$ENUM", 1, None),
    ("HT1", "ht-normal", "a normal completion containing {HT}", 1, None),
    ("HT1", "ht-interval", "( a | an ) {TN} in the inclusive interval from {E} to {E}", 1, None),
    ("HT1", "ht-record", "a Record with fields {HFL}", 1, None),
    ("HF", "ht-field", "$FIELD '(' {HT} ')'", 1, None),
    ("HT1", "ht-closure", "an Abstract Closure", 1, None),
    ("HT1", "ht-value", "{E}", 1, None),
    ("HT1", "ht-anything", "anything", 1, None),
    ("HT1", "ht-one-of", "one of {HTALT}", 2, None),
    ("HT1", "ht-list-of", "( a | an ) List of {HT}", 2, None),
    ("HT1", "ht-list-of-records", "( a | an ) List of Records with fields {HFL}", 2, None),
    ("HT1", "ht-bare", "{TN}", 2, None),
    ("HT", "ht-but-not", "{HT1} , but not {HTALT}", 2, None),
    ("HT", "ht-but-not-one", "{HT1} , but not {HT1}", 2, None),
    ("HT1", "ht-except", "any value except {HT1}", 2, None),
    ("HT1", "ht-conforms-iterresult", "( a | an ) {TN} that conforms to the IteratorResult interface", 2, None),
    ("HT1", "ht-closure-none", "an Abstract Closure with no parameters", 2, None),
    ("HT1", "ht-closure-two", "an Abstract Closure with $WORD=two parameters", 2, None),
    // tier 6: long tail, iteration 3
    (
        "P",
        "math-fn",
        "the ( cosine | sine | tangent | cube root | square root | exponential function | hyperbolic cosine | hyperbolic sine | hyperbolic tangent | inverse cosine | inverse sine | inverse tangent | inverse hyperbolic cosine | inverse hyperbolic sine | inverse hyperbolic tangent ) of {A}",
        6,
        None,
    ),
    ("P", "num-pi", "$NUM ^π", 6, None),
    ("P", "code-cun", "$CODE {CUN}", 6, None),
    ("P", "charset-string", "the CharSet containing the one string {A}", 6, None),
    ("P", "charset-all-cp", "the CharSet containing all code point values", 6, None),
    ("P", "charset-all-cu", "the CharSet containing all code unit values", 6, None),
    ("P", "charset-minus", "the CharSet containing the CharSetElements of {A} which are not also CharSetElements of {A}", 6, None),
    ("P", "charset-singles", "the CharSet containing every CharSetElement of {A} that consists of a single character", 6, None),
    ("P", "charset-empty", "the empty CharSet", 6, None),
    ("P", "returned-by", "the {TN} returned by {A}", 6, None),
    ("P", "one-char", "the one character in CharSet {A}", 6, None),
    ("P", "empty-chars", "( the | an ) empty sequence of characters", 6, None),
    ("CA", "every-single-incl", "every CharSetElement of {E} consists of a single character '(' including if {E} is empty ')'", 6, None),
    (
        "P",
        "decimal-digits",
        "the String value consisting of the digits of the decimal representation of {A} '(' in order , with no leading zeroes ')'",
        6,
        None,
    ),
    ("P", "string-solely", "the String value consisting solely of {A}", 6, None),
    ("P", "cus-first", "the first {E} code units of {A}", 6, None),
    ("P", "cus-other", "the ( other | remaining ) {E} code units of {A}", 6, None),
    ("P", "string-repr-upper-hex", "the String representation of {A} , formatted as an uppercase hexadecimal number", 6, None),
    ("P", "string-repr-lower-hex", "the String representation of {A} , formatted as a lowercase hexadecimal number", 6, None),
    ("P", "string-repr-decimal", "the String representation of {A} , formatted as a decimal number", 6, None),
    ("P", "trim-both", "the String value that is a copy of {A} with both leading and trailing white space removed", 6, None),
    ("P", "trim-leading", "the String value that is a copy of {A} with leading white space removed", 6, None),
    ("P", "trim-trailing", "the String value that is a copy of {A} with trailing white space removed", 6, None),
    ("P", "typed-var-list", "the List {A}", 6, None),
    ("P", "typed-var-string", "the String [ value ] {A}", 6, None),
    ("PRED", "unit-more-than-once-units", "contains any code unit more than once", 6, None),
    ("PRED", "unit-more-than-once-points", "contains any code point more than once", 6, None),
    ("PRED", "any-units-other-than", "contains any ( code unit | code units ) other than {ALT}", 6, None),
    ("PRED", "any-units-not-in", "contains any ( code unit | code units ) which are not in {E}", 6, None),
    ("PRED", "any-points-other-than", "contains any ( code point | code points ) other than {ALT}", 6, None),
    ("PRED", "any-points-not-in", "contains any ( code point | code points ) which are not in {E}", 6, None),
    ("P", "node-within-the", "the $NT Parse Node contained within {A}", 6, None),
    ("P", "node-within-first", "the first $NT Parse Node contained within {A}", 6, None),
    ("P", "node-within-second", "the second $NT Parse Node contained within {A}", 6, None),
    ("P", "count-nodes-within", "the number of $GRAM Parse Nodes contained within {A}", 6, None),
    ("P", "count-nodes-before", "the number of $GRAM Parse Nodes contained within {A} that either occur before {A} or contain {A}", 6, None),
    ("PRED", "contains-node-a", "contains ( a | an ) $NT Parse Node", 6, None),
    ("PRED", "not-contains-node-a", "does not contain ( a | an ) $NT Parse Node", 6, None),
    ("PRED", "not-contains-node-two", "does not contain two $NT Parse Nodes", 6, None),
    ("P", "rhs", "$CODE $NT", 6, None),
    ("P", "token-word", "the token $CODE", 6, None),
    ("P", "token-nt", "the $NT $CODE", 6, None),
    ("P", "items-in", "the List of $NT items in {A} , in source text order", 6, None),
    ("PRED", "nt-of-a", "is the $NT of ( a | an ) $NT", 6, None),
    ("PRED", "instance-var", "is an instance of $VAR", 6, None),
    ("PRED", "matched-by-either", "is matched by either {ALT}", 6, None),
    ("CA", "use-strict", "the Directive Prologue of {A} contains a Use Strict Directive", 6, None),
    ("P", "list-ints-asc", "a List of the integers in the interval from {E} '(' inclusive ')' to {E} '(' exclusive ')' , in ascending order", 6, None),
    ("P", "list-ints-desc", "a List of the integers in the interval from {E} '(' inclusive ')' to {E} '(' exclusive ')' , in descending order", 6, None),
    ("P", "elems-in-order", "a List whose elements are the elements of {A} , in order", 6, None),
    (
        "P",
        "elems-by-async-order",
        "a List whose elements are the elements of {A} , sorted by their $FIELD=AsyncEvaluationOrder field in ascending order",
        6,
        None,
    ),
    ("P", "elems-lexicographic", "a List whose elements are the elements of {A} , sorted according to lexicographic code unit order", 6, None),
    ("P", "cps-of", "the code points of {A}", 6, None),
    ("PRED", "has-no-elements", "has no elements", 6, None),
    ("PRED", "has-any-elements", "has any elements", 6, None),
    ("PRED", "has-n-elements", "has {E} elements", 6, None),
    ("P", "last-in", "the last {TN} in {A}", 6, None),
    ("Step", "foreach-backwards", "For each {TN} {V} of {E} , iterating backwards from its second-to-last element , do", 6, None),
    ("P", "elem-whose", "the element of {A} whose $FIELD [ field ] is {E}", 6, None),
    ("P", "elem-whose-tn", "the {TN} in {A} whose $FIELD [ field ] is {E}", 6, None),
    ("P", "bytes-from-at", "the sequence of {E} bytes starting with {E} ^'[' ^{E} ^']'", 6, None),
    ("P", "new-rec", "a new {REC}", 6, None),
    ("REC", "rec", "[ the ] [ {TN} ] '{' {FieldInits} '}'", 6, None),
    ("P", "new-symbol-whose", "a new Symbol whose $FIELD=Description is {E}", 6, None),
    ("P", "new-private-name-whose", "a new Private Name whose $FIELD=Description is {E}", 6, None),
    ("PRED", "contains-such", "contains ( a | an ) {TN} $VAR such that {C}", 6, None),
    ("PRED", "not-contains-such", "does not contain ( a | an ) {TN} $VAR such that {C}", 6, None),
    ("PRED", "contains-one-such", "contains exactly one {TN} $VAR such that {C}", 6, None),
    (
        "Step",
        "set-methods",
        "Set {E} 's essential internal methods [ , except for $FIELD=Call and $FIELD=Construct , ] to the [ default ordinary object ] definitions specified in $XREF .",
        6,
        None,
    ),
    ("P", "bitstring", "the $NUM=32 ^- ^bit two 's complement bit string representing {E}", 6, None),
    ("P", "ieee-convert-16", "the result of converting {E} to IEEE $NUM=754 ^- ^$NUM=2019 binary16 format [ using roundTiesToEven mode ]", 6, None),
    ("P", "ieee-convert-32", "the result of converting {E} to IEEE $NUM=754 ^- ^$NUM=2019 binary32 format [ using roundTiesToEven mode ]", 6, None),
    ("P", "ieee-convert-64", "the result of converting {E} to IEEE $NUM=754 ^- ^$NUM=2019 binary64 format [ using roundTiesToEven mode ]", 6, None),
    (
        "P",
        "bytes-decode-binary16",
        "the byte elements of {A} concatenated and interpreted as a little-endian bit string encoding of an IEEE $NUM=754 ^- ^$NUM=2019 binary16 value",
        6,
        None,
    ),
    (
        "P",
        "bytes-decode-binary32",
        "the byte elements of {A} concatenated and interpreted as a little-endian bit string encoding of an IEEE $NUM=754 ^- ^$NUM=2019 binary32 value",
        6,
        None,
    ),
    (
        "P",
        "bytes-decode-binary64",
        "the byte elements of {A} concatenated and interpreted as a little-endian bit string encoding of an IEEE $NUM=754 ^- ^$NUM=2019 binary64 value",
        6,
        None,
    ),
    (
        "P",
        "bytes-decode-signed",
        "the byte elements of {A} concatenated and interpreted as a bit string encoding of a binary little-endian two 's complement number of bit length {E}",
        6,
        None,
    ),
    (
        "P",
        "bytes-decode-unsigned",
        "the byte elements of {A} concatenated and interpreted as a bit string encoding of an unsigned little-endian binary number",
        6,
        None,
    ),
    ("CA", "mm-rel", "{E} ( happens-before | reads-from ) {E} in {E}", 6, None),
    ("P", "reads-bytes-from", "$WORD=reads-bytes-from ^{ArgsP} in {A}", 6, None),
    (
        "Step",
        "annexb-evaluated",
        "When the $NT {V} is evaluated , perform the following steps in place of the $NT Evaluation algorithm provided in $XREF :",
        6,
        None,
    ),
    (
        "Step",
        "annexb-foreach",
        "For each $NT {V} that is directly contained in the $NT of any {ALT} {V} such that {V} Contains {V} is $VAL=true , do",
        6,
        None,
    ),
    ("CA", "annexb-replacing", "replacing the $NT {E} with a $NT that has {E} as a $NT would not produce any Early Errors for {E}", 6, None),
    ("P", "component-value", "the value of the $CAP component of {A}", 6, None),
    ("PRED", "generator-ctx", "is the execution context of a generator", 6, None),
    ("P", "name-of-entry", "the Name of the entry in $XREF whose {CAPS} = {E}", 6, None),
    ("P", "intrinsic-assoc", "the intrinsic object associated with the constructor name {E} in $XREF", 6, None),
    ("Step", "set-each-index", "Set the value at each index of {A} to the value at the corresponding index of {A} .", 6, None),
    ("P", "code-unit-of", "the code unit of {A}", 6, None),
    ("P", "code-units-of-seq", "the code units of {A}", 6, None),
    ("P", "digits-single", "the single digit of {A}", 6, None),
    ("P", "digits-most-significant", "the most significant digit of {A}", 6, None),
    ("P", "digits-n", "the {E} digits of {A}", 6, None),
    ("P", "digits-most-significant-n", "the most significant {E} digits of {A}", 6, None),
    ("P", "digits-remaining-n", "the remaining {E} digits of {A}", 6, None),
    ("P", "repr-plain", "the representation of {A}", 6, None),
    ("P", "repr-decimal", "the decimal representation of {A}", 6, None),
    ("P", "repr-radix", "the representation of {A} using radix {E}", 6, None),
    ("P", "repr-decimal-radix", "the decimal representation of {A} using radix {E}", 6, None),
    ("P", "elements-of-all", "the elements of {A}", 6, None),
    ("P", "elements-of-first", "the first {E} elements of {A}", 6, None),
    ("P", "elements-of", "the [ first {E} ] elements of {A}", 6, None),
    ("Step", "remove-first-n", "Remove the first {E} elements of {A} .", 5, None),
    ("Step", "remove-these", "Remove {E} .", 6, None),
    ("PRED", "dups-none", "( has | contains ) no duplicate entries", 6, None),
    ("PRED", "dups-any", "( has | contains ) any duplicate entries", 6, Some("dups")),
    ("PRED", "env-for-not", "is not the Environment Record for ( a | an ) $NT clause", 6, None),
    ("PRED", "listed-in-column-bare", "is listed in the “ ^{CAPS} ^” column of $XREF", 6, None),
    ("PRED", "listed-in-column-tn", "is ( a | an ) {TN} listed in the “ ^{CAPS} ^” column of $XREF", 6, None),
    ("PRED", "listed-property-name", "is a $NOTREFO=<emu-not-ref> Unicode property name $NOTREFC=</emu-not-ref> listed in the “ ^$NOTREFO=<emu-not-ref> ^Property name ^$NOTREFC=</emu-not-ref> ^” column of $XREF", 6, None),
    ("PRED", "listed-property-name-or-alias", "is a $NOTREFO=<emu-not-ref> Unicode property name $NOTREFC=</emu-not-ref> or property alias listed in the “ ^$NOTREFO=<emu-not-ref> ^Property name and aliases ^$NOTREFC=</emu-not-ref> ^” column of $XREF", 6, None),
    ("PRED", "listed-property-name-or-alias-either", "is a $NOTREFO=<emu-not-ref> Unicode property name $NOTREFC=</emu-not-ref> or property alias listed in the “ ^$NOTREFO=<emu-not-ref> ^Property name and aliases ^$NOTREFC=</emu-not-ref> ^” column of $XREF or $XREF", 6, None),
    ("PRED", "listed-binary-property-or-of-strings", "is a binary Unicode property or binary property alias listed in the “ ^$NOTREFO=<emu-not-ref> ^Property name and aliases ^$NOTREFC=</emu-not-ref> ^” column of $XREF , or a binary Unicode property of strings listed in the “ ^$NOTREFO=<emu-not-ref> ^Property name ^$NOTREFC=</emu-not-ref> ^” column of $XREF", 6, None),
    ("PRED", "listed-canonical-property-name", "is a canonical , unaliased $NOTREFO=<emu-not-ref> Unicode property name $NOTREFC=</emu-not-ref> listed in the “ ^$NOTREFO=<emu-not-ref> ^Canonical property name ^$NOTREFC=</emu-not-ref> ^” column of $XREF", 6, None),
    ("PRED", "listed-binary-property-of-strings", "is a binary property of strings listed in the “ ^$NOTREFO=<emu-not-ref> ^Property name ^$NOTREFC=</emu-not-ref> ^” column of $XREF", 6, None),
    ("PRED", "has-all-slots-has", "has all of the internal slots of {T} '(' [ see ] $XREF ')'", 6, None),
    ("PRED", "has-all-slots-not", "does not have all of the internal slots of {T} '(' [ see ] $XREF ')'", 6, None),
    ("P", "char-by", "the character ( matched | represented ) by {A}", 6, None),
    ("P", "charset-containing", "the CharSet containing {E}", 6, None),
    ("P", "list-consisting", "a List consisting of {E}", 6, None),
    ("P", "cus-elements", "the [ sequence of ] code units that are the elements of {A}", 6, None),
    ("P", "nt-var", "$NT $VAR", 6, None),
    ("P", "ascii-word", "the ASCII word characters", 6, None),
    ("P", "list-syntax-errors", "a List containing one or more $VAL=SyntaxError objects", 6, None),
    ("Step", "sort-by-length", "Sort {E} according to the length of each {TN} in descending order .", 6, None),
    ("PRED", "own-prop-named", "has ( a | an ) {E} own property", 6, None),
    ("PRED", "not-own-prop-named", "does not have ( a | an ) {E} own property", 6, None),
    ("T", "a-with-no-own-props", "( a | an ) {TN} with no own properties", 6, None),
    ("T", "a-with-no-nc-props", "( a | an ) {TN} with no non-configurable properties", 6, None),
    ("PRED", "direct-binding", "( provides | does not provide ) the direct binding for this export", 6, None),
    ("PRED", "imports-binding", "imports a specific binding for this export", 6, None),
    ("PRED", "occurs-once", "occurs exactly once in {E}", 6, None),
    ("PRED", "production-in", "is an instance of a production in $XREF", 6, None),
    ("PRED", "no-entry", "does not currently contain an entry for {E}", 6, None),
    ("PRED", "cp-sequence", "is a sequence of {E} or more code points", 6, None),
    ("CA", "sufficient-bytes", "There are sufficient bytes in {E} starting at {E} to represent a value of {E}", 6, None),
    ("CA", "both-val", "{E} and {E} are both {E}", 6, None),
    ("P", "concat", "the concatenation of {EL}", 6, None),
    ("PRED", "has-component", "has a $CAP component", 6, None),
    ("PRED", "not-has-component", "does not have a $CAP component", 6, None),
    ("PRED", "neither3", "is neither {T} nor {T} nor {T}", 6, None),
    ("PRED", "same-as", "is the same {TN} as {E}", 6, None),
    ("Step", "let-see", "Let {V} be {E} '(' see $XREF ')' .", 6, None),
    ("PRED", "surrogate-value", "has the same numeric value as a leading surrogate or trailing surrogate", 6, None),
    ("PRED", "value-less-than", "has a numeric value less than {E}", 6, None),
    ("PRED", "contains-any-nt", "contains any $NT", 6, None),
    ("CA", "not-the-case", "it is not the case that [ both ] {C}", 6, None),
    ("T", "a-list-syntax-errors", "a non-empty List of $VAL=SyntaxError objects", 6, None),
    ("PRED", "has-slot-or", "has ( a | an ) $FIELD or $FIELD internal slot", 6, None),
    ("PRED", "attr-values", "has attribute values {REC}", 6, None),
    ("PRED", "any-fields", "( has | does not have ) any fields", 6, None),
    ("Step", "replace-in", "Replace {E} in {E} with {E} .", 6, None),
    ("P", "intrinsic-fn", "the intrinsic function $INTR", 6, None),
    ("Step", "append-fields", "Append {FieldEL} to {E} .", 6, None),
    ("HT", "ht-default", "{HT1} '(' default value is {E} ')'", 2, None),
    ("HT1", "ht-sequence-of", "( a | an ) sequence of {TN}", 2, None),
    ("HT1", "ht-pairs-of", "pairs of {TN}", 2, None),
    ("HT1", "ht-function-returns", "( a | an ) function that returns {HT1}", 2, None),
    ("HT1", "ht-tn-returns", "( a | an ) {TN} that returns {HT1}", 2, None),
    ("HT1", "ht-promise", "a promise", 2, None),
    ("HT1", "ht-promise-for", "a promise for {HT1}", 2, None),
    ("HT1", "ht-ge", "( a | an ) {TN} ≥ {E}", 2, None),
    ("HT1", "ht-intrinsic-keys", "a Record whose field names are intrinsic keys and whose values are objects", 2, None),
];

pub struct Grammar {
    pub rules: Vec<Rule>,
    pub by_cat: HashMap<Cat, Vec<usize>>,
    pub types: std::collections::HashSet<String>,
    pub overlay: crate::overlay::Overlay,
}

/// Inline statements (after `If C,` / `Else,`): each capitalized statement
/// template with its first word lower-cased (SI), and without its full stop
/// (SIn, before `; else`).
fn inline(rules: &[R]) -> Vec<R> {
    let mut out = Vec::new();
    for &(cat, name, tmpl, tier, sem) in rules {
        let first = tmpl.split_whitespace().next().unwrap_or("");
        if cat != "Step" || !first.starts_with(|c: char| c.is_ascii_uppercase()) || ["If", "Else", "NOTE", "For", "Repeat"].contains(&first) {
            continue;
        }
        if first.starts_with('$') || first.starts_with('{') || first.starts_with('\'') {
            continue;
        }
        let t2: &'static str = Box::leak(format!("{}{}", first.to_lowercase(), &tmpl[first.len()..]).into_boxed_str());
        out.push(("SI", name, t2, tier, sem));
        if let Some(t3) = t2.strip_suffix(" .") {
            out.push(("SIn", name, Box::leak(t3.to_string().into_boxed_str()) as &'static str, tier, sem));
        }
    }
    out
}

/// A statement pattern's inline forms: first word lower-cased (SI), and also
/// without its final full stop (SIn).
fn inline_elems(els: &[(El, bool)]) -> Vec<(Cat, Vec<(El, bool)>)> {
    let mut out = Vec::new();
    let Some((El::Lit(w), g)) = els.first() else { return out };
    if !w.starts_with(|c: char| c.is_ascii_uppercase()) || ["If", "Else", "NOTE", "For", "Repeat"].contains(&w.as_str()) {
        return out;
    }
    let mut si = els.to_vec();
    si[0] = (El::Lit(format!("{}{}", w[..1].to_lowercase(), &w[1..])), *g);
    if matches!(si.last(), Some((El::Lit(x), _)) if x == ".") {
        let mut sin = si.clone();
        sin.pop();
        out.push(("SIn", sin));
    }
    out.insert(0, ("SI", si));
    out
}

/// Whether a template's choices hold words only.
fn word_choices(ps: &[crate::decls::Piece]) -> bool {
    use crate::decls::Piece;
    ps.iter().all(|x| match x {
        Piece::Choice(alts) => alts.iter().all(|a| a.iter().all(|y| matches!(y, Piece::Word(_)))),
        _ => true,
    })
}

/// Every template a choice template stands for, one alternative per choice.
fn expansions(ps: &[crate::decls::Piece]) -> Vec<Vec<crate::decls::Piece>> {
    use crate::decls::Piece;
    let mut out: Vec<Vec<Piece>> = vec![vec![]];
    for x in ps {
        match x {
            Piece::Choice(alts) => {
                out = out.iter().flat_map(|pre| alts.iter().flat_map(|a| expansions(a)).map(move |a| [pre.clone(), a].concat())).collect();
            }
            _ => out.iter_mut().for_each(|o| o.push(x.clone())),
        }
    }
    out
}

impl Grammar {
    pub fn new(overlay: crate::overlay::Overlay) -> Result<Grammar, String> {
        let mut seen: HashMap<(Cat, &str), &str> = HashMap::new();
        for &(cat, name, tmpl, _, _) in RULES {
            if let Some(t) = seen.insert((cat, name), tmpl) {
                return Err(format!("two {cat} rules named {name}: {t:?} and {tmpl:?}"));
            }
        }
        let mut all: Vec<R> = RULES.to_vec();
        all.extend(inline(RULES));
        all.extend(crate::memmodel::RULES);
        let mut rules: Vec<Rule> =
            all.iter().enumerate().map(|(i, &(cat, name, tmpl, tier, sem))| Rule::new(i, cat, name, tmpl, tier, sem)).collect();
        for p in &overlay.phrases {
            let name: &'static str = Box::leak(p.id.clone().into_boxed_str());
            let cat = p.cat()?;
            let mut els = p.elems();
            if let Some(rn) = &p.rule {
                let built;
                let r = match rules.iter().find(|r| r.cat == cat && r.name == rn) {
                    Some(r) => r,
                    None => {
                        let &(c, n, t) = PARSER_FORMS.iter().find(|f| f.0 == cat && f.1 == rn).ok_or_else(|| format!("{}: no {cat} rule {rn}", p.id))?;
                        built = Rule::new(0, c, n, t, 6, None);
                        &built
                    }
                };
                if crate::conv::builtin_meaning(cat, rn) {
                    return Err(format!("{}: rule {rn} has a built-in meaning", p.id));
                }
                if overlay.phrases.iter().any(|q| q.id == *rn || (q.id != p.id && q.rule == p.rule && q.cat().ok() == Some(cat))) {
                    return Err(format!("{}: rule {rn} is an overlay phrase or claimed twice", p.id));
                }
                // a variable stands for an expression, a list hole (a List value), a condition (a Boolean,
                // or a condition value over the variables it binds), a type hole (its sort), a text hole
                // (its words as a String) or a bound variable
                let bare = |e: &[(El, bool)]| {
                    use crate::decls::{HoleKind, Piece};
                    crate::conv::pieces(e)
                        .into_iter()
                        .filter(|x| *x != Piece::Glue)
                        .map(|x| if matches!(x, Piece::Hole(HoleKind::L | HoleKind::C | HoleKind::T | HoleKind::Text | HoleKind::B)) { Piece::Hole(HoleKind::E) } else { x })
                        .collect::<Vec<_>>()
                };
                let fits = if p.all_alternatives {
                    let ps = bare(&r.elems);
                    ps.iter().any(|x| matches!(x, crate::decls::Piece::Choice(_))) && word_choices(&ps) && expansions(&ps).contains(&bare(&els))
                } else {
                    bare(&r.elems) == bare(&els)
                };
                if !fits {
                    return Err(format!("{}: the pattern is not rule {rn}'s template", p.id));
                }
                continue;
            }
            // an expression pattern's leading hole is a variable (a hole there would recur into P)
            if cat == "P" && matches!(els.first(), Some((El::Hole(_), _))) {
                els[0].0 = El::Hole("AV");
            }
            let mut forms = vec![(cat, els.clone())];
            if cat == "Step" {
                forms.extend(inline_elems(&els));
            }
            for (c, e) in forms {
                let i = rules.len();
                rules.push(Rule::from_elems(i, c, name, e, 6, None));
            }
        }
        for &(cat, name, tmpl, tier, sem) in crate::host::RULES {
            let i = rules.len();
            rules.push(Rule::new(i, cat, name, tmpl, tier, sem));
        }
        let mut by_cat: HashMap<Cat, Vec<usize>> = HashMap::new();
        for r in &rules {
            by_cat.entry(r.cat).or_default().push(r.idx);
        }
        Ok(Grammar { rules, by_cat, types: type_set(), overlay })
    }

    /// An overlay phrase's arguments in the order a use's holes give them, before the subject:
    /// `true` for a word choice's selector (an `alternatives="all"` claim), `false` for a variable.
    pub fn phrase_layout(&self, p: &crate::overlay::Phrase) -> Vec<bool> {
        let n = p.vars().len();
        let Some(rn) = p.rule.as_ref().filter(|_| p.all_alternatives) else { return vec![false; n] };
        let cat = p.cat().ok();
        let els = match self.rules.iter().find(|r| Some(r.cat) == cat && r.name == rn) {
            Some(r) => r.elems.clone(),
            None => match PARSER_FORMS.iter().find(|f| Some(f.0) == cat && f.1 == rn) {
                Some(&(c, n, t)) => Rule::new(0, c, n, t, 6, None).elems,
                None => return vec![false; n],
            },
        };
        crate::conv::pieces(&els)
            .iter()
            .filter_map(|x| match x {
                crate::decls::Piece::Hole(_) => Some(false),
                crate::decls::Piece::Choice(_) => Some(true),
                _ => None,
            })
            .collect()
    }

    /// The overlay phrase a rule of the category comes from, or that gives a built-in rule its meaning.
    pub fn overlay_phrase(&self, cat: &str, name: &str) -> Option<&crate::overlay::Phrase> {
        self.overlay.phrases.iter().find(|p| p.cat().ok() == Some(cat) && (p.id == name || p.rule.as_deref() == Some(name)))
    }
}
