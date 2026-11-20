//! The LR(1) automaton of the syntactic grammar, parameters expanded and
//! lookahead restrictions applied, and its conflicts (`spec-gen lr1`).
//!
//! Tokens: each literal terminal; each lexical nonterminal the grammar names,
//! a word-set one (NullLiteral, BooleanLiteral) by its words; `ID` for an
//! IdentifierName that is neither a ReservedWord nor a literal word; `$` for
//! the end. `[no LineTerminator here]` is dropped, inside restrictions too.
//! A restriction before a symbol makes restricted instances of it (`Key`);
//! one that reaches a production's end filters its reduce lookahead. States
//! with one core merge under Pager's weak compatibility, so the conflicts are
//! those of the canonical LR(1) automaton.

use jsgrammar::gl::{self, Gl, G};
use jsgrammar::grammar::{Body, Exclusion, Item, LookItem, Lookahead, Rule, Sym, Terminal};
use jsgrammar::spec::Prose;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

pub type Tok = u32;
type Seq = Vec<Tok>;
type Res = BTreeSet<Seq>;

/// The token-level grammar a rule set denotes, before parameters are expanded.
pub struct Src {
    params: HashMap<String, Vec<String>>,
    alts: HashMap<String, Vec<SrcAlt>>,
    /// Lexical nonterminals that are finite sets of words.
    words: HashMap<String, Vec<String>>,
    reserved: BTreeSet<String>,
    pub toks: Vec<String>,
    tok_ix: HashMap<String, Tok>,
    pub goals: Vec<(String, Vec<String>)>,
    pub errors: Vec<String>,
}

struct SrcAlt {
    guard: Vec<(bool, String)>,
    rhs: Vec<Item>,
    /// `Lhs : text`, with its spec.html line.
    name: String,
    nolt: bool,
}

/// A resolved right-hand-side item.
#[derive(Clone, Debug)]
enum R {
    T(Tok),
    N(String, Vec<String>),
    Look(Res),
}

const SYN_IDNAME: &str = "IdentifierName";
const SYN_ID: &str = "IdentifierName but not ReservedWord";
pub const ID: &str = "ID";
pub const EOF: &str = "$";

fn is_word(s: &str) -> bool {
    s.chars().next().is_some_and(|c| c.is_ascii_alphabetic()) && s.chars().all(|c| c.is_ascii_alphanumeric())
}

fn lit(t: &Terminal) -> Option<&str> {
    match t {
        Terminal::Text(s, _) => Some(s),
        Terminal::Cp(_) => None,
    }
}

/// The words of a lexical rule that is a finite set of words.
fn word_set(r: &Rule, lex: &HashMap<String, &Rule>, depth: usize) -> Option<Vec<String>> {
    if depth > 4 {
        return None;
    }
    let mut out = Vec::new();
    match &r.body {
        Body::OneOf(rows) => {
            for t in rows.iter().flatten() {
                out.push(lit(t).filter(|s| is_word(s))?.to_string());
            }
        }
        Body::Alts(alts) => {
            for a in alts {
                if !a.guard.is_empty() {
                    return None;
                }
                match a.rhs.as_slice() {
                    [Item::Sym(Sym::T(t), false)] => out.push(lit(t).filter(|s| is_word(s))?.to_string()),
                    [Item::Sym(Sym::Nt(n, args), false)] if args.is_empty() => {
                        out.extend(word_set(lex.get(n)?, lex, depth + 1)?)
                    }
                    _ => return None,
                }
            }
        }
    }
    Some(out)
}

impl Src {
    /// The syntactic grammar of `gl` (with Annex B's syntactic overlays if
    /// `annexb`), its goals: the spec's syntactic goals, and the supplemental
    /// and must-cover goals at every parameter setting.
    pub fn from_gl(gl: &Gl, annexb: bool) -> Src {
        let mut syn = Vec::new();
        let mut overlays = Vec::new();
        let mut lex = Vec::new();
        let mut supp = Vec::new();
        for b in &gl.blocks {
            match (b.g, &b.prose) {
                (G::Syntactic, p) => {
                    if matches!(p, Prose::Supplemental { .. }) {
                        supp.push(b.rules[0].lhs.clone());
                    }
                    syn.extend(b.rules.iter().cloned());
                }
                (G::AnnexB, Prose::Overlay { mode, .. }) if annexb => {
                    for r in b.rules.iter().filter(|r| r.colons == jsgrammar::grammar::Colons::One) {
                        overlays.push((r.clone(), *mode == "replace"));
                    }
                }
                (G::Lexical, _) => lex.extend(b.rules.iter().cloned()),
                _ => {}
            }
        }
        let mut goals: Vec<(String, Vec<(char, String)>)> = Vec::new();
        for g in &gl.spec.goals {
            let t = g.text.trim();
            let (name, args) = match t.find('[') {
                Some(k) => (&t[..k], &t[k + 1..t.len() - 1]),
                None => (t, ""),
            };
            let args = args.split(',').map(str::trim).filter(|a| !a.is_empty()).map(|a| (a.chars().next().unwrap(), a[1..].to_string())).collect();
            goals.push((name.to_string(), args));
        }
        let all: Vec<String> = supp.into_iter().chain(gl.spec.must_cover.iter().map(|g| g.text.split('[').next().unwrap_or("").trim().to_string())).collect();
        Src::new(syn, overlays, lex, goals, all)
    }

    /// `goals` with their arguments (`+P`, `~P`); `every`: goals at every setting of their parameters.
    pub fn new(syn: Vec<Rule>, overlays: Vec<(Rule, bool)>, lex: Vec<Rule>, goals: Vec<(String, Vec<(char, String)>)>, every: Vec<String>) -> Src {
        let mut s = Src {
            params: HashMap::new(),
            alts: HashMap::new(),
            words: HashMap::new(),
            reserved: BTreeSet::new(),
            toks: Vec::new(),
            tok_ix: HashMap::new(),
            goals: Vec::new(),
            errors: Vec::new(),
        };
        s.tok(EOF);
        s.tok(ID);
        let add = |s: &mut Src, r: &Rule, replace: bool| {
            let one_of: Vec<jsgrammar::grammar::Alt>;
            let alts = match &r.body {
                Body::Alts(alts) => alts,
                Body::OneOf(rows) => {
                    one_of = rows.iter().flatten().map(|t| jsgrammar::grammar::Alt {
                        guard: Vec::new(),
                        rhs: vec![Item::Sym(Sym::T(t.clone()), false)],
                        label: None,
                        text: jsgrammar::grammar::terminal_text(t),
                    }).collect();
                    &one_of
                }
            };
            s.params.entry(r.lhs.clone()).or_insert_with(|| r.params.clone());
            let v = s.alts.entry(r.lhs.clone()).or_default();
            if replace {
                v.clear();
            }
            for a in alts {
                v.push(SrcAlt {
                    guard: a.guard.clone(),
                    rhs: a.rhs.clone(),
                    name: format!("{} : {} (spec.html:{})", r.lhs, a.text, r.line),
                    nolt: a.rhs.iter().any(|i| matches!(i, Item::NoLT)),
                });
            }
        };
        for r in &syn {
            add(&mut s, r, false);
        }
        for (r, replace) in &overlays {
            add(&mut s, r, *replace);
        }
        let lexm: HashMap<String, &Rule> = lex.iter().map(|r| (r.lhs.clone(), r)).collect();
        for r in &lex {
            if let Some(w) = word_set(r, &lexm, 0) {
                s.words.insert(r.lhs.clone(), w);
            }
        }
        s.reserved = s.words.get("ReservedWord").cloned().unwrap_or_default().into_iter().collect();
        if s.reserved.is_empty() {
            s.errors.push("no ReservedWord word set".into());
        }
        let mut seen = BTreeSet::new();
        for (n, args) in goals {
            let Some(ps) = s.params.get(&n) else { continue };
            let on: Vec<String> = ps.iter().filter(|p| args.iter().any(|(c, a)| *c == '+' && a == *p)).cloned().collect();
            if seen.insert((n.clone(), on.clone())) {
                s.goals.push((n, on));
            }
        }
        for n in every {
            let Some(ps) = s.params.get(&n).cloned() else { continue };
            for m in gl::masks(ps.len()) {
                let on: Vec<String> = ps.iter().zip(&m).filter(|x| *x.1).map(|x| x.0.clone()).collect();
                if seen.insert((n.clone(), on.clone())) {
                    s.goals.push((n.clone(), on));
                }
            }
        }
        s
    }

    fn tok(&mut self, t: &str) -> Tok {
        if let Some(&k) = self.tok_ix.get(t) {
            return k;
        }
        self.toks.push(t.to_string());
        self.tok_ix.insert(t.to_string(), self.toks.len() as Tok - 1);
        self.toks.len() as Tok - 1
    }

    fn sym(&mut self, s: &Sym, on: &[String]) -> Result<R, String> {
        match s {
            Sym::T(t) => Ok(R::T(self.tok(lit(t).ok_or("a code point terminal")?))),
            Sym::Nt(n, args) => {
                if let Some(ps) = self.params.get(n) {
                    let on2 = ps
                        .iter()
                        .filter(|p| match args.iter().find(|a| &a.param == *p) {
                            Some(a) if a.sign == '+' => true,
                            Some(a) if a.sign == '?' => on.contains(p),
                            _ => false,
                        })
                        .cloned()
                        .collect();
                    Ok(R::N(n.clone(), on2))
                } else if n == SYN_IDNAME || self.words.contains_key(n) {
                    Ok(R::N(n.clone(), Vec::new()))
                } else {
                    Ok(R::T(self.tok(n)))
                }
            }
        }
    }

    fn look(&mut self, l: &Lookahead) -> Result<Res, String> {
        let seq = |s: &mut Src, xs: &[LookItem]| -> Seq {
            xs.iter().filter_map(|x| match x {
                LookItem::T(t) => lit(t).map(|t| s.tok(t)),
                LookItem::NoLT => None,
            }).collect()
        };
        match l {
            Lookahead::Ne(xs) => Ok([seq(self, xs)].into_iter().collect()),
            Lookahead::NotMem(xss) => Ok(xss.iter().map(|xs| seq(self, xs)).collect()),
            _ => Err(format!("a lookahead form the probe does not take: {l:?}")),
        }
    }

    /// Every word token: the grammar's literal words, the reserved words, and
    /// the words of the word sets it names.
    fn all_words(&mut self) -> Vec<Tok> {
        let mut ws: BTreeSet<String> = self.reserved.clone();
        for alts in self.alts.values() {
            for a in alts {
                for i in &a.rhs {
                    let mut ts = Vec::new();
                    match i {
                        Item::Sym(Sym::T(t), _) => ts.push(t),
                        Item::Sym(Sym::Nt(n, _), _) if !self.alts.contains_key(n) => ws.extend(self.words.get(n).into_iter().flatten().cloned()),
                        Item::Look(Lookahead::Ne(xs)) => ts.extend(xs.iter().filter_map(|x| if let LookItem::T(t) = x { Some(t) } else { None })),
                        Item::Look(Lookahead::NotMem(xss)) => ts.extend(xss.iter().flatten().filter_map(|x| if let LookItem::T(t) = x { Some(t) } else { None })),
                        _ => {}
                    }
                    ws.extend(ts.into_iter().filter_map(lit).filter(|s| is_word(s)).map(str::to_string));
                }
            }
        }
        ws.iter().map(|w| self.tok(w)).collect()
    }

    /// The right-hand sides of `nt` at `on`: items, the written production, the optional symbols' mask.
    fn resolve(&mut self, nt: &str, on: &[String], words: &[Tok]) -> Vec<(Vec<R>, String, String, bool)> {
        if !self.alts.contains_key(nt) && (nt == SYN_IDNAME || nt == SYN_ID) {
            let mut ts = vec![self.tok(ID)];
            ts.extend(words.iter().copied().filter(|&w| nt == SYN_IDNAME || !self.reserved.contains(&self.toks[w as usize])));
            return ts.into_iter().map(|t| (vec![R::T(t)], format!("{nt} : {}", self.toks[t as usize]), "-".into(), false)).collect();
        }
        if let Some(ws) = self.words.get(nt).cloned().filter(|_| !self.alts.contains_key(nt)) {
            return ws.iter().map(|w| (vec![R::T(self.tok(w))], format!("{nt} :: {w}"), "-".into(), false)).collect();
        }
        let mut out = Vec::new();
        let alts = std::mem::take(self.alts.get_mut(nt).unwrap());
        for a in &alts {
            if !a.guard.iter().all(|(b, p)| on.contains(p) == *b) {
                continue;
            }
            for m in gl::masks(a.rhs.iter().filter(|i| matches!(i, Item::Sym(_, true))).count()) {
                let mut k = 0;
                let mut v = Vec::new();
                let mut err = None;
                for i in &a.rhs {
                    if let Item::Sym(_, true) = i {
                        k += 1;
                        if !m[k - 1] {
                            continue;
                        }
                    }
                    let r = match i {
                        Item::Sym(s, _) => self.sym(s, on),
                        Item::Look(l) => self.look(l).map(R::Look),
                        Item::NoLT | Item::Empty => continue,
                        Item::ButNot(Sym::Nt(b, _), Exclusion::Sym(Sym::Nt(e, _))) if b == SYN_IDNAME && e == "ReservedWord" => Ok(R::N(SYN_ID.into(), Vec::new())),
                        _ => Err(format!("an item the probe does not take: {i:?}")),
                    };
                    match r {
                        Ok(r) => v.push(r),
                        Err(e) => err = Some(e),
                    }
                }
                match err {
                    Some(e) => self.errors.push(format!("{}: {e}", a.name)),
                    None => out.push((v, a.name.clone(), gl::mask_text(&m), a.nolt)),
                }
            }
        }
        *self.alts.get_mut(nt).unwrap() = alts;
        out
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Mode {
    All,
    NonEmpty,
    Empty,
}

/// A nonterminal instance: its parameters on, the token sequences none of its
/// yields may begin with (with what follows), and which of its yields it has.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Key {
    pub nt: String,
    pub on: Vec<String>,
    pub res: Vec<Seq>,
    pub mode: Mode,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum S {
    T(Tok),
    N(u32),
}

pub struct Prod {
    pub lhs: u32,
    pub rhs: Vec<S>,
    /// Tokens the reduce lookahead may not be.
    pub filter: Vec<Tok>,
    pub name: String,
    pub mask: String,
    pub nolt: bool,
}

/// The expanded grammar: instances, productions, and one start production per goal.
pub struct Cfg {
    pub keys: Vec<Key>,
    pub toks: Vec<String>,
    pub prods: Vec<Prod>,
    /// Goal instance and its start production.
    pub starts: Vec<(u32, usize)>,
    pub errors: Vec<String>,
    /// The instances with no yield.
    pub dead: Vec<u32>,
    /// The productions dropped for having a dead side.
    pub cut: Vec<Prod>,
    /// A yield of each instance, none for a dead one.
    pub yields: Vec<Option<Vec<Tok>>>,
}

struct Ex<'a> {
    src: &'a mut Src,
    words: Vec<Tok>,
    keys: Vec<Key>,
    ix: HashMap<Key, u32>,
    queue: VecDeque<u32>,
    nullable: HashMap<(String, Vec<String>), bool>,
    cache: HashMap<(String, Vec<String>), Vec<(Vec<R>, String, String, bool)>>,
}

impl Ex<'_> {
    fn alts(&mut self, nt: &str, on: &[String]) -> Vec<(Vec<R>, String, String, bool)> {
        let k = (nt.to_string(), on.to_vec());
        if !self.cache.contains_key(&k) {
            let v = self.src.resolve(nt, on, &self.words);
            self.cache.insert(k.clone(), v);
        }
        self.cache[&k].clone()
    }

    /// Nullability of every plain instance reachable from the goals.
    fn nullables(&mut self) {
        let mut seen: BTreeSet<(String, Vec<String>)> = BTreeSet::new();
        let mut work: Vec<(String, Vec<String>)> = self.src.goals.clone();
        while let Some(p) = work.pop() {
            if !seen.insert(p.clone()) {
                continue;
            }
            for (rhs, ..) in self.alts(&p.0, &p.1) {
                for r in rhs {
                    if let R::N(n, on) = r {
                        work.push((n, on));
                    }
                }
            }
        }
        let mut null: BTreeSet<(String, Vec<String>)> = BTreeSet::new();
        loop {
            let mut grew = false;
            for p in &seen {
                if null.contains(p) {
                    continue;
                }
                let ok = self.cache[p].iter().any(|(rhs, ..)| {
                    rhs.iter().all(|r| match r {
                        R::T(_) => false,
                        R::N(n, on) => null.contains(&(n.clone(), on.clone())),
                        R::Look(_) => true,
                    })
                });
                if ok {
                    null.insert(p.clone());
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        for p in seen {
            let b = null.contains(&p);
            self.nullable.insert(p, b);
        }
    }

    fn key(&mut self, k: Key) -> u32 {
        if let Some(&i) = self.ix.get(&k) {
            return i;
        }
        let i = self.keys.len() as u32;
        self.ix.insert(k.clone(), i);
        self.keys.push(k);
        self.queue.push_back(i);
        i
    }

    /// The right-hand sides `items` becomes under the restriction `s` and
    /// `mode`: symbols, the restriction left at its end, whether a token was taken.
    fn restrict(&mut self, items: &[R], s: &Res, mode: Mode) -> Vec<(Vec<S>, Res, bool)> {
        let Some((first, rest)) = items.split_first() else {
            return vec![(Vec::new(), s.clone(), false)];
        };
        let pre = |x: S, v: Vec<(Vec<S>, Res, bool)>, took: bool| -> Vec<(Vec<S>, Res, bool)> {
            v.into_iter().map(|(mut syms, r, c)| { syms.insert(0, x); (syms, r, c || took) }).collect()
        };
        match first {
            R::Look(l) => {
                let mut s2 = s.clone();
                s2.extend(l.iter().cloned());
                self.restrict(rest, &s2, mode)
            }
            R::T(t) => {
                if mode == Mode::Empty {
                    return Vec::new();
                }
                let mut tails = Res::new();
                for q in s.iter().filter(|q| q[0] == *t) {
                    if q.len() == 1 {
                        return Vec::new();
                    }
                    tails.insert(q[1..].to_vec());
                }
                let v = self.restrict(rest, &tails, Mode::All);
                pre(S::T(*t), v, true)
            }
            R::N(n, on) => {
                let mk = |res: &Res, mode| Key { nt: n.clone(), on: on.clone(), res: res.iter().cloned().collect(), mode };
                if mode == Mode::All && s.is_empty() {
                    let k = self.key(mk(s, Mode::All));
                    let v = self.restrict(rest, s, Mode::All);
                    return pre(S::N(k), v, false);
                }
                let mut out = Vec::new();
                if mode != Mode::Empty {
                    let k = self.key(mk(s, Mode::NonEmpty));
                    let v = self.restrict(rest, &Res::new(), Mode::All);
                    out.extend(pre(S::N(k), v, true));
                }
                if self.nullable.get(&(n.clone(), on.clone())).copied().unwrap_or(false) {
                    let k = self.key(mk(&Res::new(), Mode::Empty));
                    let v = self.restrict(rest, s, mode);
                    out.extend(pre(S::N(k), v, false));
                }
                out
            }
        }
    }
}

impl Cfg {
    /// Expands `src` from its goals; the instances with no yield and the
    /// productions using them are reported, the rest kept with a yield each.
    pub fn expand(src: &mut Src) -> Cfg {
        let words = src.all_words();
        let mut ex = Ex { src, words, keys: Vec::new(), ix: HashMap::new(), queue: VecDeque::new(), nullable: HashMap::new(), cache: HashMap::new() };
        ex.nullables();
        let goals = ex.src.goals.clone();
        let goal_keys: Vec<u32> = goals.iter().map(|(n, on)| ex.key(Key { nt: n.clone(), on: on.clone(), res: Vec::new(), mode: Mode::All })).collect();
        let mut prods = Vec::new();
        let mut errors = Vec::new();
        while let Some(k) = ex.queue.pop_front() {
            let key = ex.keys[k as usize].clone();
            let res: Res = key.res.iter().cloned().collect();
            for (rhs, name, mask, nolt) in ex.alts(&key.nt, &key.on) {
                for (syms, end, took) in ex.restrict(&rhs, &res, key.mode) {
                    if key.mode == Mode::NonEmpty && !took {
                        continue;
                    }
                    if end.iter().any(|q| q.len() != 1) {
                        errors.push(format!("{name}: a restriction of more than one token reaches its end"));
                        continue;
                    }
                    prods.push(Prod { lhs: k, rhs: syms, filter: end.iter().map(|q| q[0]).collect(), name: name.clone(), mask: mask.clone(), nolt });
                }
            }
        }
        let n = ex.keys.len();
        let mut live = vec![false; n];
        // each live instance's yield, from a production whose instances were live before it
        let mut yields: Vec<Option<Vec<Tok>>> = vec![None; n];
        loop {
            let mut grew = false;
            for p in &prods {
                if !live[p.lhs as usize] && p.rhs.iter().all(|s| match s { S::T(_) => true, S::N(b) => live[*b as usize] }) {
                    live[p.lhs as usize] = true;
                    let y = p.rhs.iter().flat_map(|s| match s { S::T(t) => vec![*t], S::N(b) => yields[*b as usize].clone().unwrap() }).collect();
                    yields[p.lhs as usize] = Some(y);
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        let dead: Vec<u32> = (0..n as u32).filter(|&k| !live[k as usize]).collect();
        let (kept, cut): (Vec<Prod>, Vec<Prod>) =
            prods.into_iter().partition(|p| live[p.lhs as usize] && p.rhs.iter().all(|s| match s { S::T(_) => true, S::N(b) => live[*b as usize] }));
        let mut prods = kept;
        let mut keys = ex.keys;
        let mut starts = Vec::new();
        for g in goal_keys {
            if !live[g as usize] {
                errors.push(format!("goal {} has no yield", key_name(&keys[g as usize], &ex.src.toks)));
                continue;
            }
            let mut sk = keys[g as usize].clone();
            sk.nt = format!("start {}", sk.nt);
            keys.push(sk);
            yields.push(yields[g as usize].clone());
            prods.push(Prod { lhs: keys.len() as u32 - 1, rhs: vec![S::N(g)], filter: Vec::new(), name: "start".into(), mask: "-".into(), nolt: false });
            starts.push((g, prods.len() - 1));
        }
        errors.extend(ex.src.errors.iter().cloned());
        Cfg { keys, toks: ex.src.toks.clone(), prods, starts, errors, dead, cut, yields }
    }

    pub fn sym_name(&self, s: S) -> String {
        match s {
            S::T(t) => tok_name(&self.toks[t as usize]),
            S::N(n) => key_name(&self.keys[n as usize], &self.toks),
        }
    }
}

fn tok_name(t: &str) -> String {
    if t == ID || t == EOF || t.chars().next().is_some_and(|c| c.is_ascii_uppercase()) && t.len() > 1 && t.chars().all(|c| c.is_ascii_alphanumeric()) {
        t.to_string()
    } else {
        format!("`{t}`")
    }
}

/// `Nt[+P]`, then `¬{seqs}` for a restriction, `⁺` non-empty, `ε` empty.
pub fn key_name(k: &Key, toks: &[String]) -> String {
    let mut s = k.nt.clone();
    if !k.on.is_empty() {
        s += &format!("[{}]", k.on.iter().map(|p| format!("+{p}")).collect::<Vec<_>>().join(","));
    }
    if !k.res.is_empty() {
        let seqs: Vec<String> = k.res.iter().map(|q| q.iter().map(|&t| tok_name(&toks[t as usize])).collect::<Vec<_>>().join(" ")).collect();
        s += &format!("¬{{{}}}", seqs.join(", "));
    }
    match k.mode {
        Mode::All => {}
        Mode::NonEmpty => s += "⁺",
        Mode::Empty => s += "ε",
    }
    s
}

/// A set of tokens.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TSet(Vec<u64>);

impl TSet {
    fn new(n: usize) -> TSet {
        TSet(vec![0; n.div_ceil(64)])
    }
    fn add(&mut self, t: Tok) {
        self.0[t as usize / 64] |= 1 << (t % 64);
    }
    pub fn has(&self, t: Tok) -> bool {
        self.0[t as usize / 64] >> (t % 64) & 1 == 1
    }
    /// `self ∪= o`; whether it grew.
    fn union(&mut self, o: &TSet) -> bool {
        let mut grew = false;
        for (a, b) in self.0.iter_mut().zip(&o.0) {
            grew |= *b & !*a != 0;
            *a |= b;
        }
        grew
    }
    fn minus(&mut self, o: &TSet) {
        for (a, b) in self.0.iter_mut().zip(&o.0) {
            *a &= !b;
        }
    }
    fn meets(&self, o: &TSet) -> bool {
        self.0.iter().zip(&o.0).any(|(a, b)| a & b != 0)
    }
    pub fn iter(&self) -> impl Iterator<Item = Tok> + '_ {
        (0..self.0.len() * 64).filter(|&t| self.has(t as Tok)).map(|t| t as Tok)
    }
}

type Kernel = Vec<(u32, TSet)>;

/// The automaton: kernels with lookaheads, and transitions.
pub struct Lr {
    pub kernels: Vec<Kernel>,
    pub gotos: Vec<Vec<(S, u32)>>,
    /// Start state of each start production.
    pub start_states: Vec<u32>,
    item_base: Vec<u32>,
    item_prod: Vec<u32>,
    first_after: Vec<TSet>,
    null_after: Vec<bool>,
    by_lhs: Vec<Vec<u32>>,
    filters: Vec<TSet>,
}

/// One state's conflict on a token: the shift items and the reduced productions.
/// It is an artifact of the restricted instances if its reductions are one
/// production once restrictions are erased and it has no shift.
pub struct Conflict {
    pub state: u32,
    pub tok: Tok,
    pub shifts: Vec<u32>,
    pub reduces: Vec<u32>,
}

impl Lr {
    pub fn build(g: &Cfg) -> Lr {
        Lr::build_with(g, false)
    }

    /// The automaton; `canon`: states merge only on equal kernels (canonical LR(1)).
    pub fn build_with(g: &Cfg, canon: bool) -> Lr {
        let nt = g.toks.len();
        let nk = g.keys.len();
        let mut by_lhs = vec![Vec::new(); nk];
        let mut item_base = Vec::new();
        let mut item_prod = Vec::new();
        for (i, p) in g.prods.iter().enumerate() {
            by_lhs[p.lhs as usize].push(i as u32);
            item_base.push(item_prod.len() as u32);
            item_prod.extend(std::iter::repeat_n(i as u32, p.rhs.len() + 1));
        }
        let mut first = vec![TSet::new(nt); nk];
        let mut null = vec![false; nk];
        loop {
            let mut grew = false;
            for p in &g.prods {
                let l = p.lhs as usize;
                let mut all = true;
                for s in &p.rhs {
                    match *s {
                        S::T(t) => {
                            if !first[l].has(t) {
                                first[l].add(t);
                                grew = true;
                            }
                            all = false;
                        }
                        S::N(b) => {
                            if b as usize != l {
                                let fb = first[b as usize].clone();
                                grew |= first[l].union(&fb);
                            }
                            all = null[b as usize];
                        }
                    }
                    if !all {
                        break;
                    }
                }
                if all && !null[l] {
                    null[l] = true;
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        // FIRST and nullability of each item's symbols after its next one.
        let mut first_after = vec![TSet::new(nt); item_prod.len()];
        let mut null_after = vec![true; item_prod.len()];
        for (i, p) in g.prods.iter().enumerate() {
            let b = item_base[i] as usize;
            let n = p.rhs.len();
            // suffix[d]: FIRST(rhs[d..]) and its nullability
            let mut suffix = vec![(TSet::new(nt), true); n + 1];
            for d in (0..n).rev() {
                let (mut f, mut nl) = suffix[d + 1].clone();
                match p.rhs[d] {
                    S::T(t) => {
                        f = TSet::new(nt);
                        f.add(t);
                        nl = false;
                    }
                    S::N(x) => {
                        if !null[x as usize] {
                            f = TSet::new(nt);
                            nl = false;
                        }
                        f.union(&first[x as usize]);
                    }
                }
                suffix[d] = (f, nl);
            }
            for d in 0..=n {
                (first_after[b + d], null_after[b + d]) = suffix[(d + 1).min(n)].clone();
            }
        }
        let filters = g.prods.iter().map(|p| {
            let mut s = TSet::new(nt);
            p.filter.iter().for_each(|&t| s.add(t));
            s
        }).collect();
        let mut lr = Lr { kernels: Vec::new(), gotos: Vec::new(), start_states: Vec::new(), item_base, item_prod, first_after, null_after, by_lhs, filters };
        let eof = g.toks.iter().position(|t| t == EOF).unwrap() as Tok;
        let mut by_core: HashMap<Vec<u32>, Vec<u32>> = HashMap::new();
        let mut queue = VecDeque::new();
        let mut dirty = Vec::new();
        for &(_, sp) in &g.starts {
            let mut la = TSet::new(nt);
            la.add(eof);
            let k = vec![(lr.item_base[sp], la)];
            let s = lr.place(k, canon, &mut by_core, &mut queue, &mut dirty);
            lr.start_states.push(s);
        }
        while let Some(s) = queue.pop_front() {
            dirty[s as usize] = false;
            let cl = lr.closure(g, &lr.kernels[s as usize].clone());
            let mut next: BTreeMap<S, Kernel> = BTreeMap::new();
            for (it, la) in cl {
                if let Some(x) = lr.next_sym(g, it) {
                    next.entry(x).or_default().push((it + 1, la));
                }
            }
            let mut gs = Vec::new();
            for (x, mut k) in next {
                k.sort_by_key(|e| e.0);
                let t = lr.place(k, canon, &mut by_core, &mut queue, &mut dirty);
                gs.push((x, t));
            }
            lr.gotos[s as usize] = gs;
        }
        lr
    }

    fn next_sym(&self, g: &Cfg, it: u32) -> Option<S> {
        let p = self.item_prod[it as usize];
        let d = (it - self.item_base[p as usize]) as usize;
        g.prods[p as usize].rhs.get(d).copied()
    }

    pub fn item(&self, it: u32) -> (u32, usize) {
        let p = self.item_prod[it as usize];
        (p, (it - self.item_base[p as usize]) as usize)
    }

    /// The state for kernel `k`: one with its core that is weakly compatible
    /// (`canon`: equal), its lookaheads merged in, or a new one.
    fn place(&mut self, k: Kernel, canon: bool, by_core: &mut HashMap<Vec<u32>, Vec<u32>>, queue: &mut VecDeque<u32>, dirty: &mut Vec<bool>) -> u32 {
        let core: Vec<u32> = k.iter().map(|e| e.0).collect();
        let cands = by_core.entry(core).or_default();
        for &t in cands.iter() {
            let old = &self.kernels[t as usize];
            if if canon { old.iter().zip(&k).all(|(a, b)| a.1 == b.1) } else { weakly_compatible(old, &k) } {
                let mut grew = false;
                for (o, n) in self.kernels[t as usize].iter_mut().zip(&k) {
                    grew |= o.1.union(&n.1);
                }
                if grew && !dirty[t as usize] {
                    dirty[t as usize] = true;
                    queue.push_back(t);
                }
                return t;
            }
        }
        let t = self.kernels.len() as u32;
        self.kernels.push(k);
        self.gotos.push(Vec::new());
        dirty.push(true);
        queue.push_back(t);
        cands.push(t);
        t
    }

    /// The LR(1) closure of a kernel: items and their lookaheads.
    pub fn closure(&self, g: &Cfg, k: &Kernel) -> Vec<(u32, TSet)> {
        let mut items: Vec<(u32, TSet)> = k.clone();
        let mut at: HashMap<u32, usize> = items.iter().enumerate().map(|(i, e)| (e.0, i)).collect();
        let mut queued = vec![true; items.len()];
        let mut work: Vec<usize> = (0..items.len()).collect();
        while let Some(i) = work.pop() {
            queued[i] = false;
            let it = items[i].0;
            let Some(S::N(b)) = self.next_sym(g, it) else { continue };
            let mut la = self.first_after[it as usize].clone();
            if self.null_after[it as usize] {
                la.union(&items[i].1);
            }
            for &q in &self.by_lhs[b as usize] {
                let mut m = la.clone();
                m.minus(&self.filters[q as usize]);
                let j = self.item_base[q as usize];
                match at.get(&j) {
                    Some(&x) => {
                        if items[x].1.union(&m) && !queued[x] {
                            queued[x] = true;
                            work.push(x);
                        }
                    }
                    None => {
                        at.insert(j, items.len());
                        items.push((j, m));
                        queued.push(true);
                        work.push(items.len() - 1);
                    }
                }
            }
        }
        items
    }

    /// The states reachable from the start states, each with the path of symbols to it.
    pub fn paths(&self) -> BTreeMap<u32, (usize, Vec<S>)> {
        let mut out: BTreeMap<u32, (usize, Vec<S>)> = BTreeMap::new();
        let mut q = VecDeque::new();
        for (i, &s) in self.start_states.iter().enumerate() {
            if let std::collections::btree_map::Entry::Vacant(e) = out.entry(s) {
                e.insert((i, Vec::new()));
                q.push_back(s);
            }
        }
        while let Some(s) = q.pop_front() {
            for &(x, t) in &self.gotos[s as usize] {
                if !out.contains_key(&t) {
                    let (g, mut p) = out[&s].clone();
                    p.push(x);
                    out.insert(t, (g, p));
                    q.push_back(t);
                }
            }
        }
        out
    }

    /// Every conflict of the reachable states.
    pub fn conflicts(&self, g: &Cfg, reach: &BTreeMap<u32, (usize, Vec<S>)>) -> Vec<Conflict> {
        let mut out = Vec::new();
        for &s in reach.keys() {
            let cl = self.closure(g, &self.kernels[s as usize]);
            let mut by: BTreeMap<Tok, (Vec<u32>, Vec<u32>)> = BTreeMap::new();
            for (it, la) in &cl {
                match self.next_sym(g, *it) {
                    Some(S::T(t)) => by.entry(t).or_default().0.push(*it),
                    Some(S::N(_)) => {}
                    None => {
                        for t in la.iter() {
                            by.entry(t).or_default().1.push(self.item_prod[*it as usize]);
                        }
                    }
                }
            }
            for (t, (sh, re)) in by {
                if re.len() + usize::from(!sh.is_empty()) > 1 {
                    out.push(Conflict { state: s, tok: t, shifts: sh, reduces: re });
                }
            }
        }
        out
    }
}

/// Pager's weak compatibility of two kernels with one core.
fn weakly_compatible(a: &Kernel, b: &Kernel) -> bool {
    for i in 0..a.len() {
        for j in i + 1..a.len() {
            let cross = a[i].1.meets(&b[j].1) || a[j].1.meets(&b[i].1);
            if cross && !a[i].1.meets(&a[j].1) && !b[i].1.meets(&b[j].1) {
                return false;
            }
        }
    }
    true
}

/// The report: sizes, then the conflicts grouped by their actions' written
/// productions, each state with its path and tokens, the first with its items
/// (`-v`: every state's).
pub fn report(g: &Cfg, verbose: bool) -> (String, usize) {
    let lr = Lr::build(g);
    let reach = lr.paths();
    let all = lr.conflicts(g, &reach);
    let erased = |p: u32| -> String {
        let plain = |k: u32| key_name(&Key { res: Vec::new(), mode: Mode::All, ..g.keys[k as usize].clone() }, &g.toks);
        let pr = &g.prods[p as usize];
        let rhs: Vec<String> = pr.rhs.iter().map(|&s| match s { S::T(_) => g.sym_name(s), S::N(k) => plain(k) }).collect();
        format!("{} → {}", plain(pr.lhs), rhs.join(" "))
    };
    let (cs, artifacts): (Vec<&Conflict>, Vec<&Conflict>) = all.iter().partition(|c| {
        usize::from(!c.shifts.is_empty()) + c.reduces.iter().map(|&p| erased(p)).collect::<BTreeSet<_>>().len() > 1
    });
    let item_text = |it: u32| -> String {
        let (p, d) = lr.item(it);
        let pr = &g.prods[p as usize];
        let mut v: Vec<String> = pr.rhs.iter().map(|&s| g.sym_name(s)).collect();
        v.insert(d, "·".into());
        format!("{} → {}", key_name(&g.keys[pr.lhs as usize], &g.toks), v.join(" "))
    };
    // an identifier token's own production is named by its token: one group for them all
    let named = |p: &Prod| match p.name.split_once(" : ") {
        Some((l, _)) if l == SYN_ID || l == SYN_IDNAME => format!("{l} : (the token)"),
        _ => p.name.clone(),
    };
    let mut groups: BTreeMap<Vec<String>, Vec<&Conflict>> = BTreeMap::new();
    for &c in &cs {
        let mut acts: BTreeSet<String> = BTreeSet::new();
        for &it in &c.shifts {
            let p = &g.prods[lr.item(it).0 as usize];
            acts.insert(format!("shift  {}{}", named(p), if p.nolt { " [no LT]" } else { "" }));
        }
        for &p in &c.reduces {
            let p = &g.prods[p as usize];
            acts.insert(format!("reduce {} [{}]{}", named(p), p.mask, if p.nolt { " [no LT]" } else { "" }));
        }
        groups.entry(acts.into_iter().collect()).or_default().push(c);
    }
    let mut o = String::new();
    let cores: BTreeSet<Vec<u32>> = reach.keys().map(|&s| lr.kernels[s as usize].iter().map(|e| e.0).collect()).collect();
    o += &format!(
        "lr1: {} tokens, {} instances, {} productions, {} goals, {} states ({} cores), {} conflicts in {} states, {} groups; {} restriction artifacts\n",
        g.toks.len(),
        g.keys.len() - g.starts.len(),
        g.prods.len() - g.starts.len(),
        g.starts.len(),
        reach.len(),
        cores.len(),
        cs.len(),
        cs.iter().map(|c| c.state).collect::<BTreeSet<_>>().len(),
        groups.len(),
        artifacts.len()
    );
    for e in &g.errors {
        o += &format!("error: {e}\n");
    }
    for (n, (acts, v)) in groups.iter().enumerate() {
        let mut by_state: BTreeMap<u32, Vec<&Conflict>> = BTreeMap::new();
        for &c in v {
            by_state.entry(c.state).or_default().push(c);
        }
        o += &format!("\nconflict {}: {} states, {} tokens\n", n + 1, by_state.len(), v.iter().map(|c| c.tok).collect::<BTreeSet<_>>().len());
        for a in acts {
            o += &format!("  {a}\n");
        }
        for (k, (s, cv)) in by_state.iter().enumerate() {
            let (gi, path) = &reach[s];
            let goal = key_name(&g.keys[g.starts[*gi].0 as usize], &g.toks);
            let toks: Vec<String> = cv.iter().map(|c| tok_name(&g.toks[c.tok as usize])).collect();
            o += &format!("  state {s}: {goal}: {} · {}\n", path.iter().map(|&s| g.sym_name(s)).collect::<Vec<_>>().join(" "), toks.join(" "));
            if k > 0 && !verbose {
                continue;
            }
            let c = cv[0];
            for &it in &c.shifts {
                o += &format!("    {}\n", item_text(it));
            }
            for &p in &c.reduces {
                let it = lr.item_base[p as usize] + g.prods[p as usize].rhs.len() as u32;
                o += &format!("    {}\n", item_text(it));
            }
        }
    }
    (o, cs.len())
}

/// The liveness report: instances with no yield, productions cut for using
/// one, each yield's length, and the LR(1) items with no follower their
/// restriction lets through (`canon`: of the canonical automaton).
pub fn live_report(g: &Cfg, canon: bool) -> (String, usize) {
    let lr = Lr::build_with(g, canon);
    let reach = lr.paths();
    let mut items = 0usize;
    let mut dead_items: BTreeSet<String> = BTreeSet::new();
    for &s in reach.keys() {
        for (it, la) in lr.closure(g, &lr.kernels[s as usize]) {
            items += 1;
            if la.iter().next().is_none() {
                let (p, d) = lr.item(it);
                let pr = &g.prods[p as usize];
                let mut v: Vec<String> = pr.rhs.iter().map(|&s| g.sym_name(s)).collect();
                v.insert(d, "·".into());
                dead_items.insert(format!("{} → {}", key_name(&g.keys[pr.lhs as usize], &g.toks), v.join(" ")));
            }
        }
    }
    let ys: Vec<usize> = g.yields.iter().flatten().map(|y| y.len()).collect();
    let mut o = format!(
        "live: {} instances, {} with no yield; {} productions, {} cut; {} yields, longest {}; {} states, {} LR(1) items, {} with no live follower\n",
        g.yields.len(),
        g.dead.len(),
        g.prods.len() + g.cut.len(),
        g.cut.len(),
        ys.len(),
        ys.iter().max().unwrap_or(&0),
        reach.len(),
        items,
        dead_items.len()
    );
    for &k in &g.dead {
        o += &format!("  no yield: {}\n", key_name(&g.keys[k as usize], &g.toks));
    }
    for p in &g.cut {
        o += &format!("  cut: {} [{}]\n", p.name, key_name(&g.keys[p.lhs as usize], &g.toks));
    }
    for d in &dead_items {
        o += &format!("  no live follower: {d}\n");
    }
    (o, dead_items.len())
}

/// The token classes a lexer must tell apart from the parse: `/`-class against
/// a regular expression, `}` against a template continuation.
const LEX_PAIRS: [(&str, &[&str], &[&str]); 2] = [
    ("div/regexp", &["/", "/="], &["RegularExpressionLiteral"]),
    ("}/template", &["}"], &["TemplateMiddle", "TemplateTail"]),
];

/// The lexical-goal report: each state that reads a token of both sides of a
/// `LEX_PAIRS` pair, with its goal, its symbol path and a token prefix; `shift`
/// by its own items, `next` also after reductions. Grouped per core (LR(0),
/// merged lookaheads), or per state of the canonical LR(1) automaton (`canon`).
pub fn lexgoal_report(g: &Cfg, canon: bool) -> (String, usize) {
    let lr = Lr::build_with(g, canon);
    let reach = lr.paths();
    let nt = g.toks.len();
    let mut o = String::new();
    let mut set = |names: &[&str]| {
        let mut s = TSet::new(nt);
        for n in names {
            match g.toks.iter().position(|t| t == n) {
                Some(t) => s.add(t as Tok),
                None => o += &format!("error: no token {n}\n"),
            }
        }
        s
    };
    let pairs: Vec<(&str, TSet, TSet)> = LEX_PAIRS.iter().map(|(n, a, b)| (*n, set(a), set(b))).collect();
    // per group (core, or state under `canon`): its first state, the tokens shifted and the tokens next
    let core = |s: u32| -> Vec<u32> { lr.kernels[s as usize].iter().map(|e| e.0).collect() };
    let ncores = reach.keys().map(|&s| core(s)).collect::<BTreeSet<_>>().len();
    let mut cores: BTreeMap<Vec<u32>, (u32, TSet, TSet)> = BTreeMap::new();
    for &s in reach.keys() {
        let key = if canon { vec![s] } else { core(s) };
        let e = cores.entry(key).or_insert_with(|| (s, TSet::new(nt), TSet::new(nt)));
        for (it, la) in lr.closure(g, &lr.kernels[s as usize]) {
            match lr.next_sym(g, it) {
                Some(S::T(t)) => {
                    e.1.add(t);
                    e.2.add(t);
                }
                Some(S::N(_)) => {}
                None => {
                    e.2.union(&la);
                }
            }
        }
    }
    let mut hits = 0;
    let mut body = String::new();
    for (name, a, b) in &pairs {
        let (mut shift, mut next) = (0, 0);
        let mut hit_cores = BTreeSet::new();
        for (s, sh, nx) in cores.values() {
            let both_shift = sh.meets(a) && sh.meets(b);
            if !(nx.meets(a) && nx.meets(b)) {
                continue;
            }
            hit_cores.insert(core(*s));
            if both_shift {
                shift += 1;
            } else {
                next += 1;
            }
            let (gi, path) = &reach[s];
            let goal = key_name(&g.keys[g.starts[*gi].0 as usize], &g.toks);
            let toks: Vec<String> = path.iter().flat_map(|&x| match x {
                S::T(t) => vec![t],
                S::N(k) => g.yields[k as usize].clone().unwrap_or_default(),
            }).map(|t| tok_name(&g.toks[t as usize])).collect();
            let syms: Vec<String> = path.iter().map(|&x| g.sym_name(x)).collect();
            let kind = if both_shift { "shift" } else { "next" };
            body += &format!("  {name} {kind} state {s}: {goal}: {} · | tokens: {} ·\n", syms.join(" "), toks.join(" "));
        }
        o += &format!("lexgoal {name}: {} states read both by their own items, {} more after reductions, in {} cores\n", shift, next, hit_cores.len());
        hits += shift + next;
    }
    o = format!("lexgoal: {} states, {} cores, {} groups\n{o}{body}", reach.len(), ncores, cores.len());
    (o, hits)
}

/// `spec-gen lr1 [-annexb] [-v] [-live [-canon]] [-lexgoal [-canon]]`: the report for spec.html's syntactic grammar.
pub fn run(html: &str, rest: &[String]) -> Result<bool, String> {
    let gl = Gl::load(html, None)?;
    let mut src = Src::from_gl(&gl, rest.iter().any(|a| a == "-annexb"));
    let g = Cfg::expand(&mut src);
    if rest.iter().any(|a| a == "-live") {
        let (o, n) = live_report(&g, rest.iter().any(|a| a == "-canon"));
        print!("{o}");
        return Ok(g.errors.is_empty() && n == 0);
    }
    if rest.iter().any(|a| a == "-lexgoal") {
        let (o, n) = lexgoal_report(&g, rest.iter().any(|a| a == "-canon"));
        print!("{o}");
        return Ok(g.errors.is_empty() && n == 0 && !o.contains("error:"));
    }
    print!("{}", report(&g, rest.iter().any(|a| a == "-v")).0);
    Ok(g.errors.is_empty())
}

#[cfg(test)]
mod tests {
    use super::*;
    use jsgrammar::grammar::parse_block;

    /// The conflicts of a syntactic block whose first rule is the goal.
    fn conflicts(syn: &str) -> usize {
        let rules = parse_block(syn, 1).unwrap();
        let lex = parse_block("\n  ReservedWord :: one of\n    `if` `else`\n", 1).unwrap();
        let goal = rules[0].lhs.clone();
        let mut src = Src::new(rules, Vec::new(), lex, vec![(goal, Vec::new())], Vec::new());
        let g = Cfg::expand(&mut src);
        assert!(g.errors.is_empty(), "{:?}", g.errors);
        report(&g, false).1
    }

    #[test]
    fn an_ambiguous_sum_conflicts() {
        assert_eq!(conflicts("\n  E :\n    E `+` E\n    `x`\n"), 1);
        assert_eq!(conflicts("\n  E :\n    E `+` T\n    T\n\n  T :\n    `x`\n"), 0);
    }

    #[test]
    fn a_dangling_else_is_resolved_by_its_restriction() {
        let s = |r: &str| format!("\n  S :\n    `if` `(` `x` `)` S{r}\n    `if` `(` `x` `)` S `else` S\n    `x` `;`\n");
        assert_eq!(conflicts(&s("")), 1);
        assert_eq!(conflicts(&s(" [lookahead != `else`]")), 0);
    }

    #[test]
    fn a_two_token_restriction_reaches_into_a_nonterminal() {
        let s = |r: &str| format!("\n  S :\n    {r}E `;`\n    `a` `b` `;`\n\n  E :\n    `a`\n    `a` `b`\n    `c`\n");
        assert_eq!(conflicts(&s("")), 1);
        assert_eq!(conflicts(&s("[lookahead != `a` `b`] ")), 0);
    }

    #[test]
    fn a_restriction_passes_over_an_empty_nonterminal() {
        let s = |r: &str| format!("\n  S :\n    {r}O E `;`\n    `a` `;`\n\n  O :\n    [empty]\n    `o`\n\n  E :\n    `a`\n    `c`\n");
        assert_eq!(conflicts(&s("")), 1);
        assert_eq!(conflicts(&s("[lookahead != `a`] ")), 0);
    }

    #[test]
    fn two_restricted_copies_of_one_reduction_do_not_conflict() {
        let g = "\n  S :\n    [lookahead != `a` `b`] E `x`\n    [lookahead != `a`] E `y`\n\n  E :\n    `c`\n    `a`\n    `a` `b`\n";
        assert_eq!(conflicts(g), 0);
    }

    #[test]
    fn parameters_select_alternatives() {
        let s = |a: &str| format!("\n  S :\n    A[{a}] `;`\n    `x` `;`\n\n  A[P] :\n    [+P] `x`\n    `y`\n");
        assert_eq!(conflicts(&s("+P")), 1);
        assert_eq!(conflicts(&s("~P")), 0);
    }

    #[test]
    fn an_lr1_grammar_that_is_not_lalr1_has_no_conflict() {
        let g = "\n  S :\n    `a` E `c`\n    `a` F `d`\n    `b` F `c`\n    `b` E `d`\n\n  E :\n    `e`\n\n  F :\n    `e`\n";
        assert_eq!(conflicts(g), 0);
    }

    /// The expansion of a syntactic block whose first rule is the goal.
    fn expand(syn: &str) -> Cfg {
        let rules = parse_block(syn, 1).unwrap();
        let lex = parse_block("\n  ReservedWord :: one of\n    `if` `else`\n", 1).unwrap();
        let goal = rules[0].lhs.clone();
        let mut src = Src::new(rules, Vec::new(), lex, vec![(goal, Vec::new())], Vec::new());
        Cfg::expand(&mut src)
    }

    #[test]
    fn a_restricted_instance_with_no_yield_is_reported_and_its_production_cut() {
        let g = expand("\n  S :\n    [lookahead != `a`] A\n    `b`\n\n  A :\n    `a`\n");
        assert!(g.errors.is_empty(), "{:?}", g.errors);
        let dead: Vec<String> = g.dead.iter().map(|&k| key_name(&g.keys[k as usize], &g.toks)).collect();
        assert_eq!(dead, vec!["A¬{`a`}⁺"]);
        assert_eq!(g.cut.len(), 1);
        assert_eq!(live_report(&g, true).1, 0);
    }

    #[test]
    fn each_live_instance_has_a_yield_of_its_productions() {
        let g = expand("\n  S :\n    A `c`\n\n  A :\n    A `a`\n    `b`\n");
        let toks = |k: usize| g.yields[k].as_ref().unwrap().iter().map(|&t| g.toks[t as usize].clone()).collect::<Vec<_>>().join(" ");
        assert_eq!(toks(g.starts[0].0 as usize), "b c");
        assert!(g.dead.is_empty() && g.cut.is_empty());
    }

    #[test]
    fn an_item_whose_followers_its_restriction_all_filters_has_no_live_follower() {
        let g = expand("\n  S :\n    A `x`\n    `y`\n\n  A :\n    `a` [lookahead != `x`]\n");
        assert!(g.errors.is_empty(), "{:?}", g.errors);
        assert!(g.dead.is_empty());
        for canon in [false, true] {
            let (o, n) = live_report(&g, canon);
            assert_eq!(n, 2, "{o}");
            assert!(o.contains("no live follower: A → · `a`"), "{o}");
        }
    }

    #[test]
    fn a_state_reading_a_division_and_a_regexp_is_reported() {
        let none = expand("\n  S :\n    E `;`\n\n  E :\n    E `/` P\n    P\n\n  P :\n    `x`\n    RegularExpressionLiteral\n");
        assert_eq!(lexgoal_report(&none, false).1, 0);
        let shift = expand("\n  S :\n    `a` `/` `x`\n    `a` RegularExpressionLiteral\n");
        let (o, n) = lexgoal_report(&shift, false);
        assert!(n == 1 && o.contains("div/regexp shift state") && o.contains("tokens: `a` ·"), "{o}");
        let next = expand("\n  S :\n    A `/` `x`\n\n  A :\n    `a`\n    `a` RegularExpressionLiteral\n");
        let (o, n) = lexgoal_report(&next, false);
        assert!(n == 1 && o.contains("div/regexp next state"), "{o}");
    }

    #[test]
    fn canonical_states_split_a_core_merged_lookaheads_would_report() {
        let g = expand("\n  S :\n    `a` A `/` `x`\n    `b` A RegularExpressionLiteral\n\n  A :\n    `e`\n");
        assert!(g.errors.is_empty(), "{:?}", g.errors);
        let (o, n) = lexgoal_report(&g, false);
        assert!(n == 1 && o.contains("div/regexp next state"), "{o}");
        let (o, n) = lexgoal_report(&g, true);
        assert!(n == 0 && o.contains("0 more after reductions, in 0 cores"), "{o}");
        let one = expand("\n  S :\n    A `/` `x`\n\n  A :\n    `a`\n    `a` RegularExpressionLiteral\n");
        let (o, n) = lexgoal_report(&one, true);
        assert!(n == 1 && o.contains("div/regexp next state"), "{o}");
    }
}
