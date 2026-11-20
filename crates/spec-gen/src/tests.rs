//! Unit tests: tokens print back, the disambiguation rules pick the stated
//! reading, and a small spec prints back through the data.

use crate::classify::{classify, has_tie, print};
use crate::engine::{visit, Parser};
use crate::grammar::Grammar;
use crate::token::{canon, tokenize};

fn grammar() -> Grammar {
    Grammar::new(crate::overlay::Overlay::default()).unwrap()
}

fn parse(text: &str) -> std::rc::Rc<crate::engine::Node> {
    let g = grammar();
    let mut p = Parser::new(&g, 99, false);
    p.parse(&tokenize(text), "Step").unwrap_or_else(|| panic!("no parse: {text}"))
}

#[test]
fn tokens_print_from_kind_and_value() {
    for t in ["_x_", "*\"a\\*b\"*", "*+0*<sub>𝔽</sub>", "~normal~", "|Foo[?Yield]_opt|", "%Array.prototype%", "[[Get]]", "`=>`", "0x10FFFF", "&lt;"] {
        let toks = tokenize(t);
        assert_eq!(toks.len(), 1, "{t}");
        assert_eq!(canon(&toks[0]), t);
    }
}

#[test]
fn steps_print_back() {
    let g = grammar();
    let mut p = Parser::new(&g, 99, false);
    for t in [
        "Let _x_ be ? Get(_O_, *\"length\"*).",
        "If _x_ is either *undefined* or *null*, throw a *TypeError* exception.",
        "Return the string-concatenation of _a_, _b_, and _c_.",
        "For each element _e_ of _list_, do",
        "Let _n_, _k_, and _s_ be integers such that _k_ ≥ 1, 10<sup>_k_ - 1</sup> ≤ _s_ &lt; 10<sup>_k_</sup>, and 𝔽(_s_ × 10<sup>_n_ - _k_</sup>) is _x_, choosing them so that _k_ is as small as possible.",
        "Let _e_ and _n_ be integers such that 10<sup>_f_</sup> ≤ _n_ &lt; 10<sup>_f_ + 1</sup>, choosing them so that abs(_n_ × 10<sup>_e_ - _f_</sup> - _x_) is as small as possible, then so that _n_ × 10<sup>_e_ - _f_</sup> is as large as possible.",
    ] {
        let toks = tokenize(t);
        let tree = p.parse(&toks, "Step").unwrap_or_else(|| panic!("no parse: {t}"));
        assert_eq!(print(&tree, &toks, t), t);
        assert!(!has_tie(&tree), "{t}");
    }
}

#[test]
fn maximal_munch_takes_the_operator_into_the_phrase() {
    // the substring's last hole extends over `+ _n_`
    let t = parse("Let _c_ be the substring of _s_ from _i_ to _i_ + _n_.");
    let mut top_arith = false;
    visit(&t, &mut |n| {
        if n.name == "let" {
            if let crate::engine::Item::N(e, _) = &n.items[3] {
                top_arith = e.name.starts_with("arith:");
            }
        }
    });
    assert!(!top_arith);
    // postfix binds tighter than a phrase: a copy of (_m_.[[Captures]])
    let t = parse("Let _c_ be a copy of _m_.[[Captures]].");
    let mut field_inside_copy = false;
    visit(&t, &mut |n| {
        if n.name == "copy" {
            visit(n, &mut |m| field_inside_copy |= m.name == "field");
        }
    });
    assert!(field_inside_copy);
}

#[test]
fn specificity_prefers_more_literal_words() {
    let t = parse("Let _l_ be a new empty List.");
    let mut names = Vec::new();
    visit(&t, &mut |n| names.push(n.name));
    assert!(names.contains(&"new-list") && !names.contains(&"new-thing"), "{names:?}");
}

#[test]
fn is_an_empty_list_tests_emptiness() {
    let t = parse("Assert: _e_.[[DisposableResourceStack]] is an empty List.");
    let mut names = Vec::new();
    visit(&t, &mut |n| names.push(n.name));
    assert!(names.contains(&"empty-list") && !names.contains(&"empty-coll"), "{names:?}");
}

const MINI: &str = r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _x_: an ECMAScript language value,
    ): either a normal completion containing a Boolean or a throw completion
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. If _x_ is not an Object, throw a *TypeError* exception.
    1. Let _y_ be ? Get(_x_, *"bar"*).
    1. If _y_ is *true*, then
      1. Return *true*.
    1. Else,
      1. Return *false*.
  </emu-alg>
</emu-clause>
"#;

#[test]
fn a_spec_prints_back_through_its_data() {
    let g = grammar();
    let sp = crate::spec::scan(MINI).unwrap();
    let rows = classify(&sp, &g);
    assert!(rows.iter().all(|r| r.class == crate::classify::Class::S));
    let dt = crate::data::build(MINI, &sp, &g, &rows);
    let a = &dt.algs[0];
    assert!(a.exceptions.is_empty());
    assert_eq!(a.vars.names, ["x", "y"]);
    let al = &sp.algs[a.alg];
    let out = crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent);
    assert_eq!(out, al.raw);
}

#[test]
fn sha256_known_values() {
    assert_eq!(crate::text::sha256(""), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    assert_eq!(crate::text::sha256("abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
}

const TYPE_HOLE: &str = r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _t_: a sort,
      _v_: an ECMAScript language value,
    ): a Boolean
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. If _v_ is a _t_, return *true*.
    1. If _v_ is not an _t_, return *false*.
    1. Return *false*.
  </emu-alg>
</emu-clause>
"#;

#[test]
fn a_type_hole_is_a_type() {
    let g = grammar();
    let sp = crate::spec::scan(TYPE_HOLE).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(TYPE_HOLE, &sp, &g, &rows);
    let a = &dt.algs[0];
    let body = format!("{:?}", a.body);
    assert!(body.contains(r#"IsTy(false, Or, [Var("a", 0)])"#) && body.contains(r#"IsTy(true, Or, [Var("an", 0)])"#), "{body}");
    let al = &sp.algs[a.alg];
    let out = crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent);
    assert_eq!(out, al.raw);
}

const LIST_OF_RECORDS: &str = r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _g_: a List of Records with fields [[Key]] (an ECMAScript language value) and [[Elements]] (a List of ECMAScript language values),
    ): either a normal completion containing a List of Records with fields [[Key]] (an ECMAScript language value) and [[Elements]] (a List of ECMAScript language values), or a throw completion
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. Return _g_.
  </emu-alg>
</emu-clause>
"#;

#[test]
fn a_list_of_records_is_a_header_type() {
    use crate::ast::TyExpr;
    let dt = build(LIST_OF_RECORDS);
    let a = &dt.algs[0];
    let p = a.hdr.params[0].1.as_ref().unwrap();
    assert!(matches!(p, TyExpr::ListOf(_, r) if matches!(&**r, TyExpr::Record(fs) if fs.len() == 2)), "{p:?}");
    let r = a.hdr.ret.as_ref().unwrap();
    assert!(matches!(r, TyExpr::Union(_, _, ts) if matches!(&ts[0], TyExpr::Completion(Some(t)) if **t == *p)), "{r:?}");
    let ty = |t| crate::print::ty_text(&dt.decls, &a.vars.names, t);
    assert_eq!(ty(p), "a List of Records with fields [[Key]] (an ECMAScript language value) and [[Elements]] (a List of ECMAScript language values)");
    assert_eq!(ty(r), "either a normal completion containing a List of Records with fields [[Key]] (an ECMAScript language value) and [[Elements]] (a List of ECMAScript language values), or a throw completion");
}

/// An abstract operation whose steps are `steps`, at the indentation `emu-alg` bodies have.
pub(crate) fn op(steps: &str) -> String {
    format!(
        r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo ( ): an Abstract Closure
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
{steps}
  </emu-alg>
</emu-clause>
"#
    )
}

pub(crate) fn build(html: &str) -> crate::data::Data {
    let g = grammar();
    let sp = crate::spec::scan(html).unwrap();
    let rows = classify(&sp, &g);
    crate::data::build(html, &sp, &g, &rows)
}

#[test]
fn a_closure_reads_its_call_frame() {
    let html = op("    1. Let _c_ be a new Abstract Closure with no parameters that captures nothing and performs the following steps when called:
      1. Let _args_ be the List of arguments that was passed to this function by [[Call]] or [[Construct]].
      1. If NewTarget is *undefined*, throw a *TypeError* exception.
      1. Return the *this* value.
    1. Return _c_.");
    let dt = build(&html);
    let sp = crate::spec::scan(&html).unwrap();
    let a = &dt.algs[0];
    assert!(a.exceptions.is_empty(), "{:?}", a.exceptions);
    let slot = |n: &str| a.vars.names.iter().position(|x| x == n).unwrap();
    let (t, nt, args) = (slot("#the *this* value"), slot("#NewTarget"), slot(&format!("#{}", crate::conv::ARGUMENTS)));
    assert_eq!(a.closures[0].frame, Some((t, nt, args)));
    let body = format!("{:?}", a.closures[0].body);
    assert!(!body.contains("ThisValue") && !body.contains("NewTarget") && !body.contains("Prose"), "{body}");
    assert!([t, nt, args].iter().all(|x| body.contains(&format!("Var({x})"))), "{body}");
    let lean = crate::lean::closures(&a.closures);
    assert!(lean.contains(&format!(", frame := some ({t}, {nt}, {args}) }}")), "{lean}");
    let al = &sp.algs[a.alg];
    let out = crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent);
    assert_eq!(out, al.raw);
}

#[test]
fn an_unframed_closure_has_no_frame() {
    let dt = build(&op("    1. Let _c_ be a new Abstract Closure with no parameters that captures nothing and performs the following steps when called:
      1. Return *undefined*.
    1. Return _c_."));
    assert_eq!(dt.algs[0].closures[0].frame, None);
    assert!(!crate::lean::closures(&dt.algs[0].closures).contains("frame"));
}

#[test]
#[should_panic(expected = "read outside every closure")]
fn this_outside_a_closure_of_an_operation_is_an_error() {
    build(&op("    1. Return the *this* value."));
}

#[test]
#[should_panic(expected = "both the *this* value and *this* value read")]
fn a_closure_reads_one_form_of_this() {
    build(&op("    1. Let _c_ be a new Abstract Closure with no parameters that captures nothing and performs the following steps when called:
      1. Let _a_ be the *this* value.
      1. If *this* value is *undefined*, return _a_.
      1. Return _a_.
    1. Return _c_."));
}

#[test]
#[should_panic(expected = "a read in a nested closure")]
fn a_nested_closure_reads_no_frame() {
    build(&op("    1. Let _c_ be a new Abstract Closure with no parameters that captures nothing and performs the following steps when called:
      1. Let _d_ be a new Abstract Closure with no parameters that captures nothing and performs the following steps when called:
        1. Return NewTarget.
      1. Return _d_.
    1. Return _c_."));
}

#[test]
fn calls_lists_callees_and_context_forms() {
    let html = format!(
        r#"<emu-clause id="sec-bar" type="abstract operation">
  <h1>
    Bar ( ): ~unused~
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. Return ~unused~.
  </emu-alg>
</emu-clause>
{}"#,
        op("    1. Let _x_ be the running execution context.
    1. Perform Bar().
    1. Let _c_ be a new Abstract Closure with no parameters that captures nothing and performs the following steps when called:
      1. Perform Bar().
      1. Return *undefined*.
    1. Suspend _x_.
    1. Return _c_.")
    );
    let dt = build(&html);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = crate::calls(&html, &sp, &dt);
    assert_eq!(rows, ["sec-bar\t0\tBar\t-\t\t", "sec-foo\t0\tFoo\t-\tsec-bar sec-bar\tsuspend"], "{rows:?}");
}

const TWICE_OVERLAY: &str = r#"<emu-clause id="sec-twice">
  <emu-phrase id="ph-twice" kind="expression">
    <emu-pattern>a twin of _a_ beside _a_ under _b_</emu-pattern>
    <emu-params>_a_: a Number, _b_: a Number</emu-params>
    <emu-alg>
      1. Return _a_ + _b_.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#;

const TWICE: &str = r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _x_: a Number,
      _z_: a Number,
    ): a Number
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. Let _y_ be a twin of _x_ beside _x_ under _z_.
    1. Let _w_ be a twin of _x_ beside _z_ under _z_.
    1. Return _y_.
  </emu-alg>
</emu-clause>
"#;

#[test]
fn a_repeated_pattern_variable_binds_one_expression() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-twice");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("twice.emu"), TWICE_OVERLAY).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let sp = crate::spec::scan(TWICE).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(TWICE, &sp, &g, &rows);
    let pa = &dt.phrase_algs[0];
    assert_eq!(pa.vars.names, ["a", "repeat 1", "b"]);
    assert_eq!(pa.hdr.params.len(), 3);
    let body = format!("{:?}", dt.algs[0].body);
    assert!(body.contains("Let(2, Phrase(1, [E(Var(0)), E(Var(0)), E(Var(1))]))"), "{body}");
    // _a_ bound to two expressions: no phrase
    assert!(matches!(dt.algs[0].body[1].stmt, crate::ast::Stmt::Prose(..)), "{body}");
}

/// An overlay of ph-annexb-evaluated whose emu-params are `params`.
fn evaluated_overlay(params: &str) -> String {
    format!(
        r#"<emu-clause id="sec-evaluated">
  <emu-phrase id="ph-evaluated" kind="step" rule="annexb-evaluated">
    <emu-pattern>When the _fd_ _funcDecl_ is evaluated, perform the following steps in place of the _fe_ Evaluation algorithm provided in _x_:</emu-pattern>
    <emu-params>{params}</emu-params>
    <emu-alg>
      1. Return ~unused~.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#
    )
}

#[test]
fn a_closure_step_passes_its_nested_steps_as_a_closure() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-evaluated");
    std::fs::create_dir_all(&dir).unwrap();
    let base = "_fd_: a nonterminal, _funcDecl_: a Parse Node, _fe_: a nonterminal, _x_: a clause";
    // the nested steps take one emu-params entry more than the pattern's variables
    std::fs::write(dir.join("e.emu"), evaluated_overlay(base)).unwrap();
    let e = crate::overlay::read(dir.to_str().unwrap()).err().unwrap();
    assert!(e.contains("ph-evaluated: emu-params"), "{e}");
    std::fs::write(dir.join("e.emu"), evaluated_overlay(&format!("{base}, _steps_: an Abstract Closure"))).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let html = op(r##"    1. Let _n_ be 1.
    1. Let _d_ be 2.
    1. Let _m_ be 3.
    1. When the |FunctionDeclaration| _d_ is evaluated, perform the following steps in place of the |FunctionDeclaration| Evaluation algorithm provided in <emu-xref href="#sec-foo"></emu-xref>:
      1. Let _k_ be _n_ + 1.
      1. Return ~unused~.
    1. Return _m_."##);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    let a = &dt.algs[0];
    let slot = |n: &str| a.vars.names.iter().position(|x| x == n).unwrap();
    let st = format!("{:?}", a.body[3].stmt);
    assert!(st.starts_with("Phrase(") && st.ends_with(", E(Closure(0))])"), "{st}");
    // it captures the earlier slots its body reads: _n_, not _d_ or _m_
    assert_eq!(a.closures[0].caps, [slot("n")]);
    let body = format!("{:?}", a.closures[0].body);
    assert!(body.contains(&format!("Var({})", slot("n"))) && !body.contains("Prose"), "{body}");
    let al = &sp.algs[a.alg];
    assert_eq!(crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent), al.raw);
}

const COMMA_BREAK: &str = r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _x_: an ECMAScript language value,
      _y_: an ECMAScript language value,
    ): ~unused~
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. Assert: _x_ is a Number and _y_ is a Number, or _x_ is a BigInt and _y_ is a BigInt.
    1. Return ~unused~.
  </emu-alg>
</emu-clause>
"#;

#[test]
fn a_lone_comma_connective_is_the_main_break() {
    let g = grammar();
    let sp = crate::spec::scan(COMMA_BREAK).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(COMMA_BREAK, &sp, &g, &rows);
    let a = &dt.algs[0];
    let body = format!("{:?}", a.body[0]);
    assert!(body.contains("Assert(Or(Comma, [And(Plain, [") && body.contains("]), And(Plain, ["), "{body}");
    let al = &sp.algs[a.alg];
    let out = crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent);
    assert_eq!(out, al.raw);
}

const SET_DEFINITION: &str = r##"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _F_: an Object,
    ): ~unused~
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. Set _F_.[[Call]] to the definition specified in <emu-xref href="#sec-foo"></emu-xref>.
    1. Set _F_.[[Construct]] as specified in <emu-xref href="#sec-foo"></emu-xref>.
    1. Return ~unused~.
  </emu-alg>
</emu-clause>
"##;

#[test]
fn set_definition_sets_the_place_to_the_clause_algorithm() {
    let g = grammar();
    let sp = crate::spec::scan(SET_DEFINITION).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(SET_DEFINITION, &sp, &g, &rows);
    let a = &dt.algs[0];
    let body = format!("{:?}", a.body[0]);
    assert!(body.contains("Set(Field(Var(0), ") && body.contains("Definition(Xref(\"sec-foo\", Plain, Some(0)), false)"), "{body}");
    let body = format!("{:?}", a.body[1]);
    assert!(body.contains("Set(Field(Var(0), ") && body.contains("Definition(Xref(\"sec-foo\", Plain, Some(0)), true)"), "{body}");
    let al = &sp.algs[a.alg];
    let out = crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent);
    assert_eq!(out, al.raw);
}

const CODE_POINT_TABLE: &str = r#"<emu-clause id="sec-foo">
  <h1>Foo</h1>
  <emu-table id="table-foo" caption="Foo">
    <table>
      <thead>
        <tr>
          <th>Code Point</th>
          <th>Unicode Name</th>
        </tr>
      </thead>
      <tr>
        <td>`U+0009`</td>
        <td>CHARACTER TABULATION</td>
      </tr>
      <tr>
        <td>`U+0`</td>
        <td>NULL</td>
      </tr>
    </table>
  </emu-table>
</emu-clause>
"#;

#[test]
fn a_code_point_in_code_is_a_code_point() {
    use crate::tables::Body;
    let g = grammar();
    let sp = crate::spec::scan(CODE_POINT_TABLE).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(CODE_POINT_TABLE, &sp, &g, &rows);
    let ts = crate::tables::build(CODE_POINT_TABLE, &sp, &g, &mut dt);
    let t = ts.tables[0].as_ref().unwrap();
    let body = |r: usize| format!("{:?}", t.rows[r].cells[0].body);
    assert_eq!(body(1), format!("{:?}", Body::Code(Box::new(Body::Expr(crate::ast::Expr::CodePoint(9, "0009".into(), None))))));
    // not U+ notation: kept as code
    assert!(body(2).starts_with("Expr(Code("), "{}", body(2));
    let p = crate::tables::Pr { d: &dt.decls, alg: &|_| String::new() };
    assert_eq!(crate::tables::print(&p, t), t.raw);
}

const PARAMETERIZED: &str = r#"<emu-clause id="sec-kinds">
  <h1>Kinds</h1>
  <emu-table id="table-kinds" caption="Kinds">
    <table>
      <tr><td>Alpha<br><dfn>%Alpha%</dfn></td></tr>
      <tr><td>Beta<br><dfn>%Beta%</dfn></td></tr>
    </table>
  </emu-table>
  <p>In the definitions below, references to _Kind_ should be replaced with the appropriate constructor name from the above table.</p>
  <emu-clause id="sec-kind" type="built-in function">
    <h1>_Kind_ ( _x_ )</h1>
    <emu-alg>
      1. Let _p_ be <code>"%<var>Kind</var>.prototype%"</code>.
      1. Let _q_ be *"%<var>Kind</var>.prototype%"*.
      1. Return _x_.
    </emu-alg>
  </emu-clause>
  <emu-clause id="sec-kind.prototype">
    <h1>_Kind_.prototype</h1>
    <p>The initial value of <code><var>Kind</var>.prototype</code> is a _Kind_ prototype object.</p>
  </emu-clause>
</emu-clause>
"#;

#[test]
fn a_parameterized_clause_is_read_per_instance() {
    let g = grammar();
    let sp = crate::spec::scan(PARAMETERIZED).unwrap();
    let ids: Vec<&str> = sp.clauses.iter().filter(|c| c.inst.is_some()).map(|c| c.id.as_str()).collect();
    assert_eq!(ids, ["sec-kind/Alpha", "sec-kind.prototype/Alpha", "sec-kind/Beta", "sec-kind.prototype/Beta"]);
    let beta = sp.clauses.iter().position(|c| c.id == "sec-kind/Beta").unwrap();
    assert_eq!(sp.clauses[beta].op().as_deref(), Some("Beta"));
    assert_eq!(sp.clauses[sp.home(beta)].id, "sec-kind");
    let proto = sp.clauses.iter().find(|c| c.id == "sec-kind.prototype/Alpha").unwrap();
    assert!(proto.body(PARAMETERIZED).contains("<code>Alpha.prototype</code> is a Alpha prototype object"));
    let rows = classify(&sp, &g);
    let dt = crate::data::build(PARAMETERIZED, &sp, &g, &rows);
    assert_eq!(dt.algs.len(), 2);
    for a in &dt.algs {
        let al = &sp.algs[a.alg];
        assert!(a.exceptions.is_empty(), "{:?}", a.exceptions);
        let out = crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent);
        assert_eq!(out, al.raw);
        assert!(!out.contains("<var>") && !out.contains("<code>"), "{out}");
    }
    assert!(sp.algs[dt.algs[1].alg].raw.contains("Let _p_ be *\"%Beta.prototype%\"*."));
}

const HOST_LAWS: &str = r#"<emu-clause id="sec-a">
  <h1>A</h1>
  <p>Maps must be implemented using hash tables. Sets must be implemented using hash tables.</p>
  <p>Lists must be implemented using arrays.</p>
</emu-clause>
"#;

fn host_law(tag: &str) -> Result<crate::overlay::HostLaw, String> {
    crate::overlay::host_law(tag, "why", "t.emu")
}

#[test]
fn host_law_attributes() {
    use crate::overlay::LawClass;
    let l = host_law(r#"<emu-host-law clause="sec-a" para="1" sent="0" class="nonfunctional">"#).unwrap();
    assert_eq!((l.para, l.sent, l.class, l.law), (Some(1), Some(0), LawClass::Nonfunctional, None));
    assert_eq!(host_law(r#"<emu-host-law clause="sec-a" class="law" law="jobsOrder">"#).unwrap().law.as_deref(), Some("jobsOrder"));
    for bad in [
        r#"<emu-host-law clause="sec-a" class="obligation">"#,
        r#"<emu-host-law clause="sec-a">"#,
        r#"<emu-host-law class="scope">"#,
        r#"<emu-host-law clause="sec-a" sent="0" class="scope">"#,
        r#"<emu-host-law clause="sec-a" para="x" class="scope">"#,
        r#"<emu-host-law clause="sec-a" class="law">"#,
        r#"<emu-host-law clause="sec-a" class="theorem" law="f">"#,
        r#"<emu-host-law clause="sec-a" class="law" law="a.b">"#,
    ] {
        assert!(host_law(bad).is_err(), "{bad}");
    }
    assert!(crate::overlay::host_law(r#"<emu-host-law clause="sec-a" class="scope">"#, " ", "t.emu").is_err());
}

#[test]
fn host_law_dispositions() {
    use crate::overlay::LawClass;
    let sp = crate::spec::scan(HOST_LAWS).unwrap();
    let laws = |tags: &[&str]| -> Grammar {
        let mut o = crate::overlay::Overlay::default();
        o.host_laws = tags.iter().map(|t| host_law(t).unwrap()).collect();
        Grammar::new(o).unwrap()
    };
    // the most specific law wins
    let g = laws(&[r#"<emu-host-law clause="sec-a" class="nonfunctional">"#, r#"<emu-host-law clause="sec-a" para="0" sent="1" class="advice">"#]);
    let h = crate::host::build(HOST_LAWS, &sp, &g);
    assert!(h.disp_errors.is_empty(), "{:?}", h.disp_errors);
    let got: Vec<(usize, usize, LawClass)> = h.reqs.iter().map(|r| (h.idx[r.para], r.sent, g.overlay.host_laws[r.disp.unwrap()].class)).collect();
    assert_eq!(got, vec![(0, 0, LawClass::Nonfunctional), (0, 1, LawClass::Advice), (1, 0, LawClass::Nonfunctional)]);
    // an unknown clause, a place without a requirement, two laws at one place
    for (tags, want) in [
        (&[r#"<emu-host-law clause="sec-b" class="scope">"#][..], "no such clause"),
        (&[r#"<emu-host-law clause="sec-a" para="1" sent="1" class="scope">"#][..], "no requirement sentence there"),
        (&[r#"<emu-host-law clause="sec-a" para="1" class="scope">"#, r#"<emu-host-law clause="sec-a" para="1" class="advice">"#][..], "at the same place"),
    ] {
        let h = crate::host::build(HOST_LAWS, &sp, &laws(tags));
        assert!(h.disp_errors.iter().any(|e| e.contains(want)), "{want}: {:?}", h.disp_errors);
    }
}

#[test]
fn host_law_names_its_field() {
    // a field Host.WF lacks fails the build of the module naming it
    let refs = crate::lean_host::law_refs(&[host_law(r#"<emu-host-law clause="sec-a" class="law" law="noSuchField">"#).unwrap()]);
    assert!(refs.contains("public import Ecma.Host.Laws") && refs.contains("example := @Ecma.Host.WF.noSuchField"), "{refs}");
}

const FOREACH_IN: &str = r#"<emu-clause id="sec-g">
  <h1>Grammar</h1>
  <emu-grammar type="definition">
    ExportDeclaration :
      `export` NamedExports `;`

    NamedExports :
      `{` `}`
  </emu-grammar>
</emu-clause>
<emu-clause id="sec-static-semantics-referencedbindings" type="sdo">
  <h1>Static Semantics: ReferencedBindings ( ): a List of Parse Nodes</h1>
  <dl class="header">
  </dl>
  <emu-grammar>NamedExports : `{` `}`</emu-grammar>
  <emu-alg>
    1. Return a new empty List.
  </emu-alg>
</emu-clause>
<emu-clause id="sec-e">
  <h1>Static Semantics: Early Errors</h1>
  <emu-grammar>ExportDeclaration : `export` NamedExports `;`</emu-grammar>
  <ul>
    <li>
      For each |IdentifierName| _n_ in the ReferencedBindings of |NamedExports|: It is a Syntax Error if _n_ is *"let"*.
    </li>
  </ul>
</emu-clause>
"#;

const ROW_CHILDREN: &str = r#"<emu-clause id="sec-g">
  <h1>Grammar</h1>
  <emu-grammar type="definition">
    ExportDeclaration :
      `export` NamedExports `;`
      `export` `;`

    NamedExports :
      `{` `}`
  </emu-grammar>
</emu-clause>
<emu-clause id="sec-static-semantics-exportednodes" type="sdo">
  <h1>Static Semantics: ExportedNodes ( ): a Parse Node</h1>
  <dl class="header">
  </dl>
  <emu-grammar>
    ExportDeclaration : `export` NamedExports `;`

    ExportDeclaration : `export` `;`
  </emu-grammar>
  <emu-alg>
    1. Assert: |NamedExports| is present.
    1. Return the |NamedExports|.
  </emu-alg>
  <emu-grammar>ExportDeclaration : `export` `;`</emu-grammar>
  <emu-alg>
    1. Return the |NamedExports|.
  </emu-alg>
</emu-clause>
"#;

#[test]
fn a_row_child_is_on_a_production_of_the_row() {
    let sp = crate::spec::scan(ROW_CHILDREN).unwrap();
    let dt = build(ROW_CHILDREN);
    let errs = crate::checks::row_children(&sp, &dt);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("#1: |NamedExports|"), "{errs:?}");
}

const PHRASE_CHILD_OVERLAY: &str = r#"<emu-clause id="sec-exported">
  <emu-phrase id="ph-exported" kind="expression">
    <emu-pattern>the exported names</emu-pattern>
    <emu-alg>
      1. Return the |NamedExports|.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#;

#[test]
fn a_phrase_algorithm_names_no_row_child() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-phrase-child");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("exported.emu"), PHRASE_CHILD_OVERLAY).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let sp = crate::spec::scan(ROW_CHILDREN).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(ROW_CHILDREN, &sp, &g, &rows);
    assert_eq!(dt.phrase_algs.len(), 1);
    let errs = crate::checks::row_children(&sp, &dt);
    assert_eq!(errs.len(), 2, "{errs:?}");
    assert!(errs.iter().any(|e| e.starts_with("ph-exported: |NamedExports| in a phrase algorithm")), "{errs:?}");
}

#[test]
fn foreach_in_is_an_early_sentence() {
    let sp = crate::spec::scan(FOREACH_IN).unwrap();
    let dt = build(FOREACH_IN);
    let r = &dt.early[0];
    assert!(crate::lean_early::wrapped(&dt.decls, r).is_empty(), "{:?}", crate::lean_early::wrapped(&dt.decls, r));
    let (_, src) = crate::lean_early::row(&sp, &dt.decls, r).unwrap();
    assert!(src.contains("(.forEachIn 0 (.nt \"\" ") && src.contains("(.preds (.var 0) (.isVal false .or [(.val (.str \"let\" \"\"))]) [])"), "{src}");
}

#[test]
fn nt_of_a_is_a_predicate_of_its_subject() {
    let dt = build(&op("    1. Let _body_ be the |FunctionBody| of |GeneratorBody|.
    1. If _body_ is the |FunctionBody| of an |AsyncFunctionBody|, return *false*.
    1. Return *true*."));
    let a = &dt.algs[0];
    let body = format!("{:?}", a.body[1]);
    let p = dt.decls.phrases.iter().position(|p| p.cat == "PRED" && p.name == "nt-of-a").unwrap();
    assert!(body.contains(&format!("Preds(Var(0), Phrase({p}, [E(Nt(")), "{body}");
}

#[test]
fn a_possessive_reads_the_named_component() {
    let html = op("    1. Let _ctx_ be the running execution context.
    1. Return _ctx_'s LexicalEnvironment.");
    let dt = build(&html);
    let a = &dt.algs[0];
    let body = format!("{:?}", a.body[1]);
    let f = dt.decls.fields.get("LexicalEnvironment").unwrap();
    assert!(body.contains(&format!("Phrase(")) && body.contains(&format!("Field({f})")), "{body}");
    let p = dt.decls.phrases.iter().find(|p| p.cat == "P" && p.name == "poss").unwrap();
    assert!(matches!(&p.meaning, Some(crate::decls::Meaning::Prim { prim, .. }) if dt.decls.prims.name(*prim) == "Component"));
    let sp = crate::spec::scan(&html).unwrap();
    let al = &sp.algs[a.alg];
    assert_eq!(crate::print::body(&dt.decls, &a.vars.names, &a.closures, &a.body, al.base, al.close_indent), al.raw);
}

const AT_LEAST_OVERLAY: &str = r#"<emu-clause id="formal-types">
  <emu-phrase id="ph-type-at-least" kind="type" subject="_v_" rule="ht-ge" alternatives="all">
    <emu-pattern>an _t_ ≥ _lo_</emu-pattern>
    <p>"a" and "an" are one article.</p>
    <emu-params>_t_: a type, _lo_: an extended mathematical value, _v_: anything</emu-params>
    <emu-alg>
      1. If _v_ is not a _t_, return *false*.
      1. If _v_ ≥ _lo_, return *true*.
      1. Return *false*.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#;

const AT_LEAST: &str = r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _n_: an integer ≥ 2,
    ): ~unused~
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. Return ~unused~.
  </emu-alg>
</emu-clause>
"#;

#[test]
fn a_lower_bound_type_is_the_overlay_type_phrase() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-at-least");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("types.emu"), AT_LEAST_OVERLAY).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let sp = crate::spec::scan(AT_LEAST).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(AT_LEAST, &sp, &g, &rows);
    let p = dt.decls.phrases.iter().position(|p| p.cat == "HT1" && p.name == "ht-ge").unwrap();
    assert!(matches!(dt.decls.phrases[p].meaning, Some(crate::decls::Meaning::Alg(_))));
    let hdr = format!("{:?}", dt.algs[0].hdr.params);
    assert!(hdr.contains(&format!("Phrase({p}, [W(1), T(Sort(")), "{hdr}");
}

const FLAG: &str = r#"<emu-clause id="sec-foo" type="abstract operation">
  <h1>
    Foo (
      _pattern_: a List,
      _flags_: a String,
    ): a Boolean
  </h1>
  <dl class="header">
  </dl>
  <emu-alg>
    1. If _flags_ is *"i"*, let _i_ be *true*; else let _i_ be *false*.
    1. For each element _e_ of _pattern_, do
      1. Let _d_ be _e_.
    1. If _flags_ is *"m"*, then
      1. Let _m_ be *true*.
    1. Let _n_ be the count of _pattern_'s elements.
    1. Return _i_.
  </emu-alg>
</emu-clause>
"#;

/// The checks' messages on FLAG, its step 4 read as a loop over `_v_`.
fn flag_checks(v: &str) -> Vec<String> {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join(format!("spec-gen-flag-{v}"));
    std::fs::create_dir_all(&dir).unwrap();
    let sp = crate::spec::scan(FLAG).unwrap();
    let (_, step) = crate::spec::labelled(&sp.algs[0].steps).into_iter().find(|(p, _)| p == "4").unwrap();
    let reading = format!(
        "<emu-clause id=\"t\">\n  <emu-reading clause=\"sec-foo\" steps=\"4\" hashes=\"{}\">\n    <emu-alg reading=\"definition\">\n      1. Let _n_ be 0.\n      1. For each element _{v}_ of _pattern_, do\n        1. Set _n_ to _n_ + 1.\n    </emu-alg>\n  </emu-reading>\n</emu-clause>\n",
        crate::text::sha256(&step.text)
    );
    std::fs::write(dir.join("t.emu"), reading).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(FLAG, &sp, &g, &rows);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    crate::checks::check(&sp, &g, &dt).into_iter().filter(|m| m.contains("a reading binds")).collect()
}

#[test]
fn a_reading_does_not_rebind_a_live_variable() {
    assert_eq!(flag_checks("i"), ["sec-foo #0: a reading binds _i_, which is bound on every path to the step it replaces"]);
    assert_eq!(flag_checks("pattern").len(), 1);
    // a finished loop's variables, a one-armed branch's, a fresh one
    for v in ["e", "d", "m", "k"] {
        assert!(flag_checks(v).is_empty(), "{v}");
    }
}

#[test]
fn readings_replace_their_own_algorithms_step() {
    let r = crate::overlay::Anchor { clause: "c".into(), step: "2".into(), hash: "h2".into(), alts: vec![], also: vec![("3".into(), "h3".into())] };
    // two algorithms of one clause share step 2; the reading's text is the second's
    let steps = [("c", 0, "2", "x".to_string()), ("c", 1, "2", "h2".to_string()), ("c", 1, "3", "h3".to_string()), ("d", 2, "2", "h2".to_string())];
    let a = crate::anchored_steps(std::iter::once(&r), &steps);
    assert_eq!(a, vec![(1, "2"), (1, "3")]);
    assert!(!crate::is_read(&a, 0, "2"));
    assert!(!crate::is_read(&a, 2, "2"));
    assert!(crate::is_read(&a, 1, "2") && crate::is_read(&a, 1, "2.a") && crate::is_read(&a, 1, "3.b.i"));
    assert!(!crate::is_read(&a, 1, "20") && !crate::is_read(&a, 1, "2a"));
}

#[test]
fn pinned_steps_of_definition_readings_are_not_used() {
    let t = r#"[(.readings 3 (.let_ 1 (.phrase 7 [.text ")"])) [(.definition, [(.phrase 8 [])])]), (.readings 4 (.phrase 9 []) [(.test262, [])])]"#;
    let u = crate::without_pinned(t);
    assert!(!u.contains(".phrase 7") && u.contains(".phrase 8") && u.contains(".phrase 9"), "{u}");
}

#[test]
fn the_overlay_grammar_defines_every_nonterminal_it_names() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-grammar");
    std::fs::create_dir_all(&dir).unwrap();
    let block = |rules: &str| format!("<emu-clause id=\"g\">\n  <emu-grammar type=\"definition\">\n{rules}  </emu-grammar>\n</emu-clause>\n");
    std::fs::write(dir.join("g.emu"), block("    A ::\n      B? `x`\n")).unwrap();
    let e = crate::overlay::read(dir.to_str().unwrap()).err().unwrap();
    assert!(e.contains("A names B"), "{e}");
    std::fs::write(dir.join("g.emu"), block("    A ::\n      B? `x`\n\n    B :: one of\n      `&#x0000;` ` `\n")).unwrap();
    let o = crate::overlay::read(dir.to_str().unwrap()).unwrap();
    assert_eq!(o.grammar.iter().map(|r| r.lhs.as_str()).collect::<Vec<_>>(), ["A", "B"]);
}

#[test]
fn permanent_steps_claim_residue() {
    use crate::overlay::{permanent, StepClass};
    let p = |c: &str, s: &str| permanent(&format!(r#"<emu-permanent clause="{c}" step="{s}" class="assert-future">"#), "why", "t.emu").unwrap();
    let steps: Vec<(String, String)> = [("sec-a#0", "1"), ("sec-a#1", "1"), ("sec-b#0", "2.a"), ("ph-x", "2")].iter().map(|(k, s)| (k.to_string(), s.to_string())).collect();
    // a clause claims the step in each of its algorithms, `#n` in one; an overlay id claims its own
    let (by, errs) = crate::residue::claim(&steps, &[p("sec-a#1", "1"), p("sec-b", "2.a"), p("ph-x", "2")]);
    assert!(errs.is_empty(), "{errs:?}");
    assert_eq!(by, vec![None, Some(0), Some(1), Some(2)]);
    // stale: no residue step there; two entries on one step
    let (_, errs) = crate::residue::claim(&steps, &[p("sec-b", "2")]);
    assert!(errs.iter().any(|e| e.contains("no residue step there")), "{errs:?}");
    let (_, errs) = crate::residue::claim(&steps, &[p("sec-a", "1"), p("sec-a#0", "1")]);
    assert!(errs.iter().any(|e| e.contains("claims the step that")), "{errs:?}");
    // an unknown class, a missing step or reason
    let l = permanent(r#"<emu-permanent clause="sec-a" step="1" class="informative">"#, "why", "t.emu").unwrap();
    assert_eq!(l.class, StepClass::Informative);
    let l = permanent(r#"<emu-permanent clause="sort-a" step="2" class="history">"#, "why", "t.emu").unwrap();
    assert_eq!(l.class, StepClass::History);
    for (tag, body) in [
        (r#"<emu-permanent clause="sec-a" step="1" class="assert">"#, "why"),
        (r#"<emu-permanent clause="sec-a" class="informative">"#, "why"),
        (r#"<emu-permanent step="1" class="informative">"#, "why"),
        (r#"<emu-permanent clause="sec-a" step="1" class="informative">"#, " "),
    ] {
        assert!(permanent(tag, body, "t.emu").is_err(), "{tag}");
    }
}

#[test]
fn definition_readings_drop_their_pinned_side() {
    use crate::ast::Reading::{Definition, Literal};
    let t = r#"(.readings 0 [(.phrase 7 [(.text "a ] ( \" b")])] [(.definition, [(.phrase 8 [])])]), (.readings 1 (.phrase 9 []) [])"#;
    assert_eq!(super::without_defined(t, &[Definition, Literal]), r#"(.readings 0 [(.definition, [(.phrase 8 [])])]), (.readings 1 (.phrase 9 []) [])"#);
}

/// A spec of 18 empty clauses and a clause 19 holding `body`.
fn realm_spec(body: &str) -> String {
    let mut s: String = (1..=18).map(|n| format!("<emu-clause id=\"sec-c{n}\">\n  <h1>C{n}</h1>\n</emu-clause>\n")).collect();
    s.push_str(&format!("<emu-clause id=\"sec-c19\">\n  <h1>C19</h1>\n{body}</emu-clause>\n"));
    s
}

const REALM_OBJS: &str = r#"  <emu-clause id="sec-object-prototype">
    <h1>Properties of the Object Prototype Object</h1>
    <p>The <dfn>Object prototype object</dfn>:</p>
    <ul>
      <li>is <dfn>%Object.prototype%</dfn>.</li>
      <li>has a [[Prototype]] internal slot whose value is *null*.</li>
    </ul>
  </emu-clause>
  <emu-clause id="sec-function-prototype">
    <h1>Properties of the Function Prototype Object</h1>
    <p>The <dfn>Function prototype object</dfn>:</p>
    <ul>
      <li>is <dfn>%Function.prototype%</dfn>.</li>
      <li>has a [[Prototype]] internal slot whose value is %Object.prototype%.</li>
    </ul>
  </emu-clause>
  <emu-clause id="sec-foo-object">
    <h1>The Foo Object</h1>
    <p>The <dfn>%Foo%</dfn> object:</p>
    <ul>
      <li>is an ordinary object.</li>
    </ul>
"#;

fn realm(fns: &str) -> crate::realm::Realm {
    let html = realm_spec(&format!("{REALM_OBJS}{fns}  </emu-clause>\n"));
    let sp = crate::spec::scan(&html).unwrap();
    crate::realm::build(&html, &sp, &[]).unwrap()
}

fn builtin(id: &str, h1: &str, extra: &str) -> String {
    format!("    <emu-clause id=\"{id}\" type=\"built-in function\">\n      <h1>{h1}</h1>\n      <p>This function performs the following steps when called:</p>\n      <emu-alg>\n        1. Return *undefined*.\n      </emu-alg>\n{extra}    </emu-clause>\n")
}

#[test]
fn realm_defaults_follow_section_18() {
    let r = realm(&builtin("sec-foo.bar", "Foo.bar ( _x_ [ , _y_ ] )", ""));
    let (op, fp, foo, bar) = (r.by_name("Object.prototype").unwrap(), r.by_name("Function.prototype").unwrap(), r.by_name("Foo").unwrap(), r.by_path("Foo.bar").unwrap());
    assert_eq!(r.objs[op].proto, None);
    assert_eq!(r.objs[foo].proto, Some(op), "a non-function's default [[Prototype]]");
    assert_eq!(r.objs[bar].proto, Some(fp), "a function's default [[Prototype]]");
    assert!(r.objs[bar].extensible && r.objs[foo].extensible);
    let f = r.objs[bar].fun.as_ref().unwrap();
    assert_eq!(f.length, 1, "optional parameters are not counted");
    assert_eq!(crate::realm::name_string(&f.prefix, &f.name), "bar");
    assert!(!f.ctor);
    assert_eq!(f.length_attrs, crate::realm::FUN_PROP_ATTRS);
    let p = &r.objs[foo].props[0];
    assert_eq!(p.attrs, crate::realm::DATA_ATTRS);
    assert_eq!(p.val, crate::realm::PVal::Data(crate::realm::Val::Obj(bar)));
    assert!(r.objs.iter().enumerate().all(|(i, o)| o.proto.is_none_or(|p| p < i)), "creation order");
}

#[test]
fn realm_reads_length_sentences_accessors_and_symbol_keys() {
    let r = realm(&[
        builtin("sec-foo.bar", "Foo.bar ( ..._args_ )", "      <p>The *\"length\"* property of this method is *2*<sub>𝔽</sub>.</p>\n"),
        builtin("sec-get-foo.baz", "get Foo.baz", ""),
        builtin("sec-foo-%symbol.iterator%", "Foo [ %Symbol.iterator% ] ( )", ""),
    ]
    .concat());
    let foo = r.by_name("Foo").unwrap();
    let fun = |p: &str| r.objs[r.by_path(p).unwrap()].fun.clone().unwrap();
    assert_eq!(fun("Foo.bar").length, 2);
    let g = fun("get Foo.baz");
    assert_eq!((crate::realm::name_string(&g.prefix, &g.name), g.length), ("get baz".to_string(), 0));
    let it = fun("Foo [ %Symbol.iterator% ]");
    assert_eq!(crate::realm::name_string(&it.prefix, &it.name), "[Symbol.iterator]");
    let baz = r.objs[foo].props.iter().find(|p| p.key == crate::realm::Key::Str("baz".into())).unwrap();
    assert_eq!(baz.attrs, crate::realm::ACCESSOR_ATTRS);
    assert_eq!(baz.val, crate::realm::PVal::Accessor { get: r.by_path("get Foo.baz"), set: None }, "a missing half is undefined");
}

#[test]
fn realm_rejects_an_unread_bullet() {
    let html = realm_spec(&format!("{}      <li>has a mystery.</li>\n    </ul>\n  </emu-clause>\n", REALM_OBJS.trim_end_matches("    </ul>\n")));
    let sp = crate::spec::scan(&html).unwrap();
    let e = crate::realm::build(&html, &sp, &[]).err().unwrap();
    assert!(e.contains("sec-foo-object") && e.contains("an unread bullet"), "{e}");
}

fn value(id: &str, h1: &str, body: &str) -> String {
    format!("    <emu-clause id=\"{id}\">\n      <h1>{h1}</h1>\n{body}    </emu-clause>\n")
}

fn realm_err(body: &str) -> String {
    let html = realm_spec(&format!("{REALM_OBJS}{body}  </emu-clause>\n"));
    let sp = crate::spec::scan(&html).unwrap();
    crate::realm::build(&html, &sp, &[]).err().unwrap()
}

const WELL_KNOWN_SYMBOLS: &str = "  <emu-table id=\"table-well-known-symbols\">\n    <table>\n      <thead><tr><th>Specification Name</th></tr></thead>\n      <tr><td>%Symbol.iterator%</td></tr>\n    </table>\n  </emu-table>\n";

#[test]
fn realm_reads_value_sentences() {
    use crate::realm::{Key, PVal, Val};
    let attrs = "      <p>This property has the attributes { [[Writable]]: *false*, [[Enumerable]]: *false*, [[Configurable]]: *false* }.</p>\n";
    let r = realm(&[
        WELL_KNOWN_SYMBOLS,
        &value("sec-foo.self", "Foo.self", "      <p>The initial value of `Foo.self` is %Foo%.</p>\n"),
        &value("sec-foo.proto", "Foo.proto", &format!("      <p>The value of `Foo.proto` is the Object prototype object.</p>\n{attrs}")),
        &value("sec-foo.empty", "Foo.empty", "      <p>The initial value of `Foo.empty` is the empty String.</p>\n"),
        &value("sec-foo.name", "Foo.name", "      <p>The initial value of `Foo.name` is *\"Foo\"*.</p>\n"),
        &value("sec-foo.iterator", "Foo.iterator", "      <p>The initial value of `Foo.iterator` is the well-known symbol %Symbol.iterator% (<emu-xref href=\"#table-well-known-symbols\"></emu-xref>).</p>\n"),
        &value("sec-foo.big", "Foo.big", "      <p>The value of `Foo.big` is *-9007199254740991*<sub>𝔽</sub> (𝔽(-(2<sup>53</sup> - 1))).</p>\n"),
        &value("sec-foo.nan", "Foo.nan", "      <p>The value of `Foo.nan` is *NaN*.</p>\n"),
        &value("sec-foo.inf", "Foo.inf", "      <p>The value of `Foo.inf` is *+∞*<sub>𝔽</sub>.</p>\n"),
        &value("sec-foo.pi", "Foo.pi", "      <p>The Number value for π, the ratio of the circumference of a circle to its diameter, which is approximately 3.1415926535897932.</p>\n"),
        &value("sec-foo-%symbol.tostringtag%", "Foo [ %Symbol.toStringTag% ]", "      <p>The initial value of the %Symbol.toStringTag% property is the String value *\"Foo\"*.</p>\n"),
    ]
    .concat());
    let foo = r.by_name("Foo").unwrap();
    let get = |k: Key| r.objs[foo].props.iter().find(|p| p.key == k).unwrap().clone();
    let v = |k: &str| get(Key::Str(k.into())).val;
    assert_eq!(v("self"), PVal::Data(Val::Obj(foo)));
    assert_eq!(v("proto"), PVal::Data(Val::Obj(r.by_name("Object.prototype").unwrap())));
    assert_eq!(get(Key::Str("proto".into())).attrs, crate::realm::Attrs { writable: false, enumerable: false, configurable: false });
    assert_eq!(get(Key::Str("self".into())).attrs, crate::realm::DATA_ATTRS);
    assert_eq!(v("empty"), PVal::Data(Val::Str(String::new())));
    assert_eq!(v("name"), PVal::Data(Val::Str("Foo".into())));
    assert_eq!(v("iterator"), PVal::Data(Val::Sym("Symbol.iterator".into())));
    assert_eq!(v("big"), PVal::Data(Val::Number((-9007199254740991.0f64).to_bits())));
    assert_eq!(v("nan"), PVal::Data(Val::Number(0x7FF8_0000_0000_0000)));
    assert_eq!(v("inf"), PVal::Data(Val::Number(f64::INFINITY.to_bits())));
    assert_eq!(v("pi"), PVal::Data(Val::Number(std::f64::consts::PI.to_bits())));
    assert_eq!(get(Key::Sym("Symbol.toStringTag".into())).val, PVal::Data(Val::Str("Foo".into())));
}

#[test]
fn realm_rejects_an_unread_value() {
    let e = realm_err(&value("sec-foo.x", "Foo.x", "      <p>The value of `Foo.x` is the Number value for τ, which is approximately 6.28.</p>\n"));
    assert!(e.contains("sec-foo.x") && e.contains("an unread value"), "{e}");
    let e = realm_err(&value("sec-foo.y", "Foo.y", "      <p>The value of `Foo.z` is *1*<sub>𝔽</sub>.</p>\n"));
    assert!(e.contains("a value sentence of another property"), "{e}");
}

#[test]
fn realm_described_numbers_round_their_approximations() {
    for (d, bits) in crate::realm::DESCRIBED {
        let x = d.rsplit("approximately ").next().unwrap().replace(" × 10^", "e");
        assert_eq!(x.parse::<f64>().unwrap().to_bits(), *bits, "{d}");
    }
}

#[test]
fn realm_reads_the_global_object() {
    use crate::realm::{Key, PVal, Val};
    let table6 = "  <emu-table id=\"table-well-known-intrinsic-objects\">\n    <table>\n      <thead><tr><th>Intrinsic Name</th><th>Global Name</th></tr></thead>\n      <tr>\n        <td>%Foo%</td>\n        <td>*\"Foo\"*</td>\n      </tr>\n    </table>\n  </emu-table>\n";
    let global = format!(
        "  <emu-clause id=\"sec-global-object\">\n    <h1>The Global Object</h1>\n{}{}{}{}  </emu-clause>\n",
        value("sec-undefined", "undefined", "      <p>The initial value of the *\"undefined\"* property of the global object is *undefined* (see <emu-xref href=\"#sec-c1\"></emu-xref>).</p>\n      <p>This property has the attributes { [[Writable]]: *false*, [[Enumerable]]: *false*, [[Configurable]]: *false* }.</p>\n"),
        value("sec-globalthis", "globalThis", "      <p>The initial value of the *\"globalThis\"* property of the global object in a Realm Record _realm_ is _realm_.[[GlobalEnv]].[[GlobalThisValue]].</p>\n"),
        builtin("sec-isfoo", "isFoo ( _x_ )", "").replace("<p>This function", "<p><dfn>%isFoo%</dfn>. This function"),
        value("sec-g-foo", "Foo ( . . . )", "      <p>See <emu-xref href=\"#sec-foo-object\"></emu-xref>.</p>\n"),
    );
    let omit = "  <emu-clause id=\"sec-foo-note\">\n    <h1>Foo Note</h1>\n    <p>A host may omit the *\"Foo\"* property of the global object.</p>\n  </emu-clause>\n";
    let html = realm_spec(&format!("{table6}{REALM_OBJS}  </emu-clause>\n{global}{omit}"));
    let sp = crate::spec::scan(&html).unwrap();
    let r = crate::realm::build(&html, &sp, &[]).unwrap();
    let g = |k: &str| r.globals.iter().find(|p| p.key == Key::Str(k.into())).unwrap().clone();
    assert_eq!(g("undefined").val, PVal::Data(Val::Undefined));
    assert!(!g("undefined").attrs.writable);
    assert_eq!(g("globalThis").val, PVal::Data(Val::GlobalThis));
    assert_eq!(g("isFoo").val, PVal::Data(Val::Obj(r.by_name("isFoo").unwrap())));
    assert_eq!(g("Foo").val, PVal::Data(Val::Obj(r.by_name("Foo").unwrap())));
    assert!(g("Foo").omittable && !g("Foo").optional && !g("isFoo").omittable);
    assert_eq!(r.globals.iter().map(|p| p.key.clone()).collect::<Vec<_>>(), ["undefined", "globalThis", "isFoo", "Foo"].map(|k| Key::Str(k.into())), "clause order");
}

#[test]
fn intrinsic_default_literals_name_realm_objects() {
    let ops = r#"<emu-clause id="sec-c1">
  <h1>C1</h1>
  <emu-clause id="sec-getprototypefromconstructor" type="abstract operation">
    <h1>GetPrototypeFromConstructor ( _ctor_: a function object, _intrinsicDefaultProto_: a String, ): an Object</h1>
    <dl class="header"></dl>
    <emu-alg>
      1. Return _ctor_.
    </emu-alg>
  </emu-clause>
  <emu-clause id="sec-a" type="abstract operation">
    <h1>A ( _f_: a function object, ): an Object</h1>
    <dl class="header"></dl>
    <emu-alg>
      1. Let _p_ be GetPrototypeFromConstructor(_f_, *"%Foo%"*).
      1. Return GetPrototypeFromConstructor(_f_, *"Foo"*).
    </emu-alg>
  </emu-clause>
</emu-clause>
"#;
    let html = realm_spec(&format!("{REALM_OBJS}  </emu-clause>\n")).replacen("<emu-clause id=\"sec-c1\">\n  <h1>C1</h1>\n</emu-clause>\n", ops, 1);
    let sp = crate::spec::scan(&html).unwrap();
    let r = crate::realm::build(&html, &sp, &[]).unwrap();
    let dt = build(&html);
    let errs = crate::checks::intrinsic_defaults(&sp, &dt, &r);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].contains("\"Foo\""), "{errs:?}");
}

#[test]
fn realm_reads_optional_clauses_attribute_bullets_and_accessor_sentences() {
    use crate::realm::{Attrs, Key, PVal, Val};
    let html = realm_spec(&format!(
        "{}      <li>has a *\"length\"* property whose initial value is *+0*<sub>𝔽</sub> and whose attributes are {{ [[Writable]]: *true*, [[Enumerable]]: *false*, [[Configurable]]: *false* }}.</li>\n    </ul>\n{}{}  </emu-clause>\n",
        REALM_OBJS.trim_end_matches("    </ul>\n"),
        builtin("sec-foo.old", "Foo.old ( )", "").replace("<emu-clause id=\"sec-foo.old\"", "<emu-clause id=\"sec-foo.old\" legacy normative-optional"),
        value("sec-foo.acc", "Foo.acc", &format!("      <p>`Foo.acc` is an accessor property with attributes {{ [[Enumerable]]: *false*, [[Configurable]]: *false* }}. The [[Getter]] and [[Setter]] attributes are defined as follows:</p>\n{}", builtin("sec-get-foo.acc", "get Foo.acc", ""))),
    ));
    let sp = crate::spec::scan(&html).unwrap();
    let r = crate::realm::build(&html, &sp, &[]).unwrap();
    let foo = &r.objs[r.by_name("Foo").unwrap()];
    let p = |k: &str| foo.props.iter().find(|p| p.key == Key::Str(k.into())).unwrap();
    assert!(p("old").optional && r.objs[r.by_path("Foo.old").unwrap()].optional);
    assert_eq!((p("length").val.clone(), p("length").attrs), (PVal::Data(Val::Number(0)), Attrs { writable: true, enumerable: false, configurable: false }));
    assert_eq!(p("acc").attrs, Attrs { writable: false, enumerable: false, configurable: false });
}

#[test]
fn realm_rejects_a_prototype_cycle() {
    let html = realm_spec(&format!(
        "{REALM_OBJS}    </ul>\n  </emu-clause>\n  <emu-clause id=\"sec-bar\">\n    <h1>Bar</h1>\n    <p>The <dfn>%Bar%</dfn> object:</p>\n    <ul>\n      <li>has a [[Prototype]] internal slot whose value is %Baz%.</li>\n    </ul>\n    <p>The <dfn>%Baz%</dfn> object:</p>\n    <ul>\n      <li>has a [[Prototype]] internal slot whose value is %Bar%.</li>\n    </ul>\n  </emu-clause>\n"
    ));
    let sp = crate::spec::scan(&html).unwrap();
    let e = crate::realm::build(&html, &sp, &[]).err().unwrap();
    assert!(e.contains("a [[Prototype]] cycle among Bar, Baz"), "{e}");
}

#[test]
fn a_multi_step_reading_covers_its_later_sibling_steps() {
    let html = op("    1. Let _x_ be 1.
    1. Let _y_ be 2.
    1. Return _x_.");
    let sp = crate::spec::scan(&html).unwrap();
    let hs: Vec<String> = crate::spec::labelled(&sp.algs[0].steps).iter().map(|(_, t)| crate::text::sha256(&t.text)).collect();
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-covered");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("r.emu"), format!(r#"<emu-clause id="formal-r">
  <emu-reading clause="sec-foo" steps="1 2" hashes="{} {}">
    <emu-alg reading="definition">
      1. Let _x_ be 3.
    </emu-alg>
  </emu-reading>
</emu-clause>
"#, hs[0], hs[1])).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    let body = &dt.algs[0].body;
    // step 2 is read by step 1's reading: under each reading, no steps of its own
    let (s1, s2) = (format!("{:?}", body[0]), format!("{:?}", body[1]));
    assert!(s1.contains("Readings(0, ") && s1.contains("(Definition, [Node"), "{s1}");
    assert!(s2.contains("Readings(0, ") && s2.ends_with("[(Definition, [])]) }"), "{s2}");
    assert!(!format!("{:?}", body[2]).contains("Readings("));
}

#[test]
fn a_definition_reading_of_an_erratum_step_reads_its_literal_text() {
    let html = op("    1. Let _x_ be 1.
    1. Return _x_.");
    let sp = crate::spec::scan(&html).unwrap();
    let h = crate::text::sha256(&crate::spec::labelled(&sp.algs[0].steps)[0].1.text);
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-nested");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("r.emu"), format!(r#"<emu-clause id="formal-r">
  <emu-erratum id="erratum-X" name="X" resolution="literal" stops="">
    <emu-reading clause="sec-foo" step="1" hash="{h}">
      <emu-alg reading="proposed">
        1. Let _x_ be 2.
      </emu-alg>
    </emu-reading>
  </emu-erratum>
  <emu-reading clause="sec-foo" steps="1" hashes="{h}">
    <emu-alg reading="definition">
      1. Let _x_ be 3.
    </emu-alg>
  </emu-reading>
</emu-clause>
"#)).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    // the erratum's readings outside, the definition reading of the literal step inside
    let s = format!("{:?}", dt.algs[0].body[0]);
    assert!(s.contains("Readings(0, Readings(1, ") && s.contains("(Definition, [Node") && s.contains("(Proposed, [Node"), "{s}");
}

/// Data for Foo and Bar under the errata of `errata` (emu-erratum elements).
fn stop_sites(name: &str, errata: &str) -> crate::data::Data {
    let html = op("    1. Let _x_ be 1.
    1. Assert: _x_ is 1.
    1. If _x_.[[A]].[[B]] is 1, return ! Bar().
    1. Return _x_.") + &op("    1. Return Foo().").replace("sec-foo", "sec-bar").replace("Foo (", "Bar (");
    let sp = crate::spec::scan(&html).unwrap();
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("r.emu"), format!("<emu-clause id=\"formal-r\">\n{errata}</emu-clause>\n")).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let rows = classify(&sp, &g);
    crate::data::build(&html, &sp, &g, &rows)
}

#[test]
fn a_stop_site_labels_its_checks_and_a_caller_its_calls() {
    let dt = stop_sites("spec-gen-stops", r#"  <emu-erratum id="erratum-X" name="X" resolution="literal" stops="sec-foo@2 sec-foo@3"></emu-erratum>
  <emu-erratum id="erratum-Y" name="Y" resolution="literal" stops="sec-bar@1[sec-foo]"></emu-erratum>
"#);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    let foo = dt.algs.iter().find(|a| dt.decls.clauses.names[a.clause] == "sec-foo").unwrap();
    let (s1, s2, s3) = (format!("{:?}", foo.body[0].stmt), format!("{:?}", foo.body[1].stmt), format!("{:?}", foo.body[2].stmt));
    assert!(!s1.contains("Erratum") && !s1.contains("At("), "{s1}");
    assert!(s2.starts_with("AssertAt(Some(0), "), "{s2}");
    // a field read of a field's value, the `!`, and the call of Bar under the caller condition
    assert!(s3.contains("Erratum(0, true, Field(Field(Var("), "{s3}");
    assert!(s3.contains("BangAt(0, Erratum(1, true, Call(Alg("), "{s3}");
    let bar = dt.algs.iter().find(|a| dt.decls.clauses.names[a.clause] == "sec-bar").unwrap();
    assert!(!format!("{:?}", bar.body).contains("Erratum"));
    // under a caller condition the site's Asserts are checks with no erratum, the caller's call labelled
    let dt = stop_sites("spec-gen-stops-caller", r#"  <emu-erratum id="erratum-Z" name="Z" resolution="literal" stops="sec-foo@2[sec-bar]"></emu-erratum>
"#);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    let foo = dt.algs.iter().find(|a| dt.decls.clauses.names[a.clause] == "sec-foo").unwrap();
    let s2 = format!("{:?}", foo.body[1].stmt);
    assert!(s2.starts_with("AssertAt(None, "), "{s2}");
    let bar = dt.algs.iter().find(|a| dt.decls.clauses.names[a.clause] == "sec-bar").unwrap();
    assert!(format!("{:?}", bar.body).contains("Erratum(0, true, Call(Alg("));
    // a caller that never calls the site's clause is an error
    let dt = stop_sites("spec-gen-stops-nowhere", r#"  <emu-erratum id="erratum-Y" name="Y" resolution="literal" stops="sec-foo@1[sec-foo]"></emu-erratum>
"#);
    assert!(dt.anchor_errors.iter().any(|e| e.contains("calls sec-foo nowhere")), "{:?}", dt.anchor_errors);
}

#[test]
fn a_step_patch_puts_its_steps_first_and_nests_an_algorithm_under_the_last() {
    let html = op("    1. Let _x_ be 1.
    1. Return _x_.") + &op("    1. Return 2.").replace("sec-foo", "sec-bar").replace("Foo (", "Bar (");
    let patched = |patch: &str, hash: Option<&str>| {
        let mut sp = crate::spec::scan(&html).unwrap();
        let foo = sp.algs.iter().position(|a| a.clause.is_some_and(|c| sp.clauses[c].id == "sec-foo")).unwrap();
        let hash = hash.map_or_else(|| crate::text::sha256(&sp.algs[foo].raw), str::to_string);
        let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-step-patch");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("r.emu"), format!("<emu-clause id=\"formal-r\">\n  {}\n</emu-clause>\n", patch.replace("HASH", &hash))).unwrap();
        let ov = crate::overlay::read(dir.to_str().unwrap()).unwrap();
        crate::overlay::patch(&mut sp, &ov).map(|()| sp.algs.swap_remove(foo))
    };
    let gate = "<emu-step-patch clause=\"sec-foo\" alg=\"0\" hash=\"HASH\"><emu-alg>\n      1. If _x_ is 0, return 0.\n    </emu-alg></emu-step-patch>";
    let a = patched(gate, None).unwrap();
    let texts: Vec<&str> = a.steps.iter().map(|s| s.text.as_str()).collect();
    assert_eq!(texts, ["If _x_ is 0, return 0.", "Let _x_ be 1.", "Return _x_."]);
    let nest = gate.replace("hash=\"HASH\"", "hash=\"HASH\" nest=\"sec-bar 0\"").replace(", return 0.", ", then");
    let a = patched(&nest, None).unwrap();
    assert_eq!(a.steps.len(), 3);
    assert_eq!(a.steps[0].kids.iter().map(|s| s.text.as_str()).collect::<Vec<_>>(), ["Return 2."]);
    // the patched algorithm's text must be the one the patch was written against
    assert!(patched(gate, Some("0")).is_err_and(|e| e.contains("the algorithm's hash is")));
}

#[test]
fn a_proposed_erratum_has_no_stops() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-proposed");
    std::fs::create_dir_all(&dir).unwrap();
    let emu = |a: &str| format!(r#"<emu-clause id="formal-r">
  <emu-erratum id="erratum-X" name="X" {a}>
    <emu-note>
      <p>The proposed text.</p>
    </emu-note>
  </emu-erratum>
</emu-clause>
"#);
    std::fs::write(dir.join("r.emu"), emu(r#"resolution="proposed""#)).unwrap();
    let o = crate::overlay::read(dir.to_str().unwrap()).unwrap();
    assert_eq!((o.errata[0].resolution.as_str(), o.errata[0].stops.len()), ("proposed", 0));
    // a proposed erratum never stops; an unknown resolution is refused
    for a in [r#"resolution="proposed" stops="""#, r#"resolution="adopted""#] {
        std::fs::write(dir.join("r.emu"), emu(a)).unwrap();
        assert!(crate::overlay::read(dir.to_str().unwrap()).is_err(), "{a}");
    }
}

#[test]
fn one_emu_alg_reads_test262_and_proposed() {
    let html = op("    1. Let _x_ be 1.
    1. Return _x_.");
    let sp = crate::spec::scan(&html).unwrap();
    let h = crate::text::sha256(&crate::spec::labelled(&sp.algs[0].steps)[0].1.text);
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-both");
    std::fs::create_dir_all(&dir).unwrap();
    let emu = |r: &str| format!(r#"<emu-clause id="formal-r">
  <emu-erratum id="erratum-X" name="X" resolution="test262">
    <emu-reading clause="sec-foo" step="1" hash="{h}">
      <emu-alg reading="{r}">
        1. Let _x_ be 2.
      </emu-alg>
    </emu-reading>
  </emu-erratum>
</emu-clause>
"#);
    std::fs::write(dir.join("r.emu"), emu("test262 proposed")).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    // one alternative in the overlay, both readings in the data, converted once
    let s = format!("{:?}", dt.algs[0].body[0]);
    assert!(s.contains("(Test262, [Node") && s.contains("(Proposed, [Node"), "{s}");
    assert_eq!(dt.algs[0].readings.len(), 1);
    assert_eq!(crate::data::overlay_steps(&g).iter().filter(|(k, _)| k.starts_with("erratum-X/")).map(|(k, _)| k.as_str()).collect::<Vec<_>>(), ["erratum-X/sec-foo@1/test262+proposed"]);
    // a reading twice, or one the erratum cannot have, is refused
    for r in ["test262 test262", "proposed definition"] {
        std::fs::write(dir.join("r.emu"), emu(r)).unwrap();
        assert!(crate::overlay::read(dir.to_str().unwrap()).is_err(), "{r}");
    }
}

#[test]
fn a_test262_erratum_may_say_where_its_literal_text_stops() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-stops-t262");
    std::fs::create_dir_all(&dir).unwrap();
    let emu = |attrs: &str| format!("<emu-clause id=\"formal-r\">\n  <emu-erratum id=\"erratum-X\" name=\"X\" {attrs}>\n  </emu-erratum>\n</emu-clause>\n");
    let read = |attrs: &str| {
        std::fs::write(dir.join("r.emu"), emu(attrs)).unwrap();
        crate::overlay::read(dir.to_str().unwrap())
    };
    let o = read(r#"resolution="test262" stops="sec-foo@1""#).unwrap();
    assert!(o.errata[0].stops_given && o.errata[0].stops.len() == 1 && o.errata[0].stops[0].clause == "sec-foo");
    let o = read(r#"resolution="test262""#).unwrap();
    assert!(!o.errata[0].stops_given && o.errata[0].stops.is_empty());
    assert!(read(r#"resolution="literal""#).is_err());
}

const ROW_ERRATUM: &str = r#"<emu-clause id="sec-g">
  <h1>Grammar</h1>
  <emu-grammar type="definition">
    ExportDeclaration :
      NamedExports
      `export` `;`
      `export` NamedExports `;`
      `from` FromClause

    NamedExports :
      `{` `}`

    FromClause :
      `f`
  </emu-grammar>
</emu-clause>
<emu-clause id="sec-static-semantics-exportednames" type="sdo">
  <h1>Static Semantics: ExportedNames ( ): a List of Strings</h1>
  <dl class="header">
  </dl>
  <emu-grammar>NamedExports : `{` `}`</emu-grammar>
  <emu-alg>
    1. Return a new empty List.
  </emu-alg>
</emu-clause>
<emu-annex id="sec-annex">
  <h1>Annex</h1>
  <emu-annex id="sec-exportednames-annex">
    <h1>Static Semantics: ExportedNames</h1>
    <p>The semantics of ExportedNames is extended as follows:</p>
  </emu-annex>
</emu-annex>
"#;

#[test]
fn an_erratum_row_reads_the_chain_rule_literally() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-row-erratum");
    std::fs::create_dir_all(&dir).unwrap();
    let emu = |clause: &str, grammar: &str, alg: &str| format!(r#"<emu-clause id="formal-r">
  <emu-erratum id="erratum-X" name="X" resolution="test262">
    <emu-reading id="row-x" clause="{clause}" grammar="{grammar}">
      <emu-alg{alg}>
        1. Return « "x" ».
      </emu-alg>
    </emu-reading>
  </emu-erratum>
</emu-clause>
"#);
    let sp = crate::spec::scan(ROW_ERRATUM).unwrap();
    let data_in = |clause: &str, grammar: &str| {
        std::fs::write(dir.join("r.emu"), emu(clause, grammar, r#" reading="test262 proposed""#)).unwrap();
        let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
        let rows = classify(&sp, &g);
        crate::data::build(ROW_ERRATUM, &sp, &g, &rows)
    };
    let data = |grammar: &str| data_in("sec-static-semantics-exportednames", grammar);
    let dt = data("ExportDeclaration : NamedExports");
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    let r = &dt.reading_rows[0];
    assert_eq!(r.erratum, Some(0));
    // the literal reading is the chain rule: ExportedNames of the sole child
    let s = format!("{:?}", r.body);
    assert!(s.starts_with("[Node { attrs: ") && s.contains("stmt: Readings(0, ") && s.contains("(Test262, [Node") && s.contains("(Proposed, [Node"), "{s}");
    assert_eq!(r.steps().len(), 1);
    assert!(!format!("{:?}", r.steps()).contains("Readings("));
    assert!(!r.annex);
    // beside terminals, a nonterminal without a row of the SDO: the same literal reading, also from an annex clause
    for (clause, annex) in [("sec-static-semantics-exportednames", false), ("sec-exportednames-annex", true)] {
        let dt = data_in(clause, "ExportDeclaration : `from` FromClause");
        assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
        let r = &dt.reading_rows[0];
        assert_eq!((r.erratum, r.annex, r.sdo.as_str()), (Some(0), annex, "ExportedNames"));
        let s = format!("{:?}", r.body);
        assert!(s.contains("stmt: Readings(0, ") && s.contains("Sdo(") && s.contains("Child("), "{s}");
    }
    // not a nonterminal whose SDO has a row, nor terminals alone, and only with both readings
    for grammar in ["ExportDeclaration : `export` NamedExports `;`", "ExportDeclaration : `export` `;`"] {
        let dt = data(grammar);
        assert!(dt.anchor_errors.iter().any(|e| e.contains("row-x: an erratum's row is for a chain production")), "{:?}", dt.anchor_errors);
    }
    // an erratum with one reading (switch="none"): its row is that reading, for any production
    for grammar in ["ExportDeclaration : `export` NamedExports `;`", "ExportDeclaration : `export` `;`"] {
        let one = emu("sec-static-semantics-exportednames", grammar, r#" reading="test262 proposed""#)
            .replace(r#"resolution="test262">"#, r#"resolution="test262" switch="none">"#);
        std::fs::write(dir.join("r.emu"), one).unwrap();
        let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
        let rows = classify(&sp, &g);
        let dt = crate::data::build(ROW_ERRATUM, &sp, &g, &rows);
        assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
        let r = &dt.reading_rows[0];
        assert_eq!(r.erratum, None);
        assert!(!format!("{:?}", r.body).contains("Readings("));
    }
    // an annex clause extends an SDO only by its own paragraphs, not its nested clauses'
    let dt = data_in("sec-annex", "ExportDeclaration : `from` FromClause");
    assert!(dt.anchor_errors.iter().any(|e| e.contains("row-x: no SDO clause sec-annex")), "{:?}", dt.anchor_errors);
    std::fs::write(dir.join("r.emu"), emu("sec-static-semantics-exportednames", "ExportDeclaration : NamedExports", "")).unwrap();
    assert!(crate::overlay::read(dir.to_str().unwrap()).is_err());
}

#[test]
fn a_covered_else_joins_its_if_under_the_reading() {
    let html = op("    1. Let _x_ be 1.
    1. If _x_ is 1, then
      1. Set _x_ to 2.
    1. Else,
      1. Set _x_ to 3.
    1. Return _x_.");
    let sp = crate::spec::scan(&html).unwrap();
    let ls = crate::spec::labelled(&sp.algs[0].steps);
    let h = |p: &str| crate::text::sha256(&ls.iter().find(|(q, _)| q == p).unwrap().1.text);
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-covered-else");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("r.emu"), format!(r#"<emu-clause id="formal-r">
  <emu-reading clause="sec-foo" steps="2 3" hashes="{} {}">
    <emu-alg reading="definition">
      1. Set _x_ to 4.
    </emu-alg>
  </emu-reading>
</emu-clause>
"#, h("2"), h("3"))).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    assert!(dt.algs[0].exceptions.is_empty(), "{:?}", dt.algs[0].exceptions);
    let body = &dt.algs[0].body;
    assert_eq!(body.len(), 3);
    use crate::ast::Stmt;
    let Stmt::Readings(0, lit, alts) = &body[1].stmt else { panic!("{:?}", body[1]) };
    assert!(matches!(&**lit, Stmt::If(_, _, arms, Some(_)) if arms.is_empty()), "{lit:?}");
    assert_eq!(alts.len(), 1);
}

/// Data for a reading on `steps` of an If/Else algorithm.
fn else_reading(name: &str, steps: &[&str]) -> (crate::spec::Spec, Grammar, crate::data::Data) {
    let html = op("    1. Let _x_ be 1.
    1. If _x_ is 1, then
      1. Set _x_ to 2.
    1. Else,
      1. Set _x_ to 3.
    1. Return _x_.");
    let sp = crate::spec::scan(&html).unwrap();
    let ls = crate::spec::labelled(&sp.algs[0].steps);
    let h = |p: &str| crate::text::sha256(&ls.iter().find(|(q, _)| q == p).unwrap().1.text);
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    let hs: Vec<String> = steps.iter().map(|p| h(p)).collect();
    std::fs::write(dir.join("r.emu"), format!(r#"<emu-clause id="formal-r">
  <emu-reading clause="sec-foo" steps="{}" hashes="{}">
    <emu-alg reading="definition">
      1. Set _x_ to 4.
    </emu-alg>
  </emu-reading>
</emu-clause>
"#, steps.join(" "), hs.join(" "))).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    (sp, g, dt)
}

#[test]
fn an_else_anchor_is_an_error_and_its_prose_is_reported() {
    let (sp, g, dt) = else_reading("spec-gen-else-anchor", &["3"]);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    let ex = &dt.algs[0].exceptions;
    assert!(ex.iter().any(|(_, w)| w.contains("an erratum anchored on an Else step")), "{ex:?}");
    let errs = crate::checks::check(&sp, &g, &dt);
    assert!(errs.iter().any(|e| e.ends_with("1 Else step(s) kept as prose")), "{errs:?}");
}

#[test]
fn a_covered_else_away_from_its_reading_is_an_error() {
    let (sp, g, dt) = else_reading("spec-gen-else-stray", &["1", "3"]);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    let ex = &dt.algs[0].exceptions;
    assert!(ex.iter().any(|(_, w)| w.contains("a covered Else step without its reading")), "{ex:?}");
    let errs = crate::checks::check(&sp, &g, &dt);
    assert!(errs.iter().any(|e| e.ends_with("1 Else step(s) kept as prose")), "{errs:?}");
}

#[test]
fn asserts_lists_each_site_with_its_class() {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-asserts");
    std::fs::create_dir_all(&dir).unwrap();
    let defined = "Assert: _x_ is the answer to everything.";
    std::fs::write(
        dir.join("t.emu"),
        format!(
            r#"<emu-clause id="t">
  <emu-permanent clause="sec-foo" step="3" class="assert-future">A later step.</emu-permanent>
  <emu-permanent clause="sec-foo" step="4" class="assert-provenance">Where _x_ came from.</emu-permanent>
  <emu-reading clause="sec-foo" steps="5" hashes="{}">
    <emu-alg reading="definition">
      1. Assert: _x_ is *true*.
    </emu-alg>
  </emu-reading>
</emu-clause>
"#,
            crate::text::sha256(defined)
        ),
    )
    .unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let html = op(&format!(
        "    1. Let _x_ be ! Foo().
    1. Assert: _x_ is *true*.
    1. Assert: The following step will succeed.
    1. Assert: _x_ came from the moon.
    1. {defined}
    1. Assert: _x_ is made of green cheese.
    1. Return _x_."
    ));
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    let got: Vec<(&str, String, String)> = crate::asserts::sites(&sp, &g, &dt).into_iter().map(|s| (s.class, s.key, s.path)).collect();
    let site = |c: &'static str, k: &str, p: &str| (c, k.to_string(), p.to_string());
    let def = "definition-sec-foo-5/sec-foo@5/definition";
    assert_eq!(
        got,
        vec![
            site("bang", "sec-foo#0", "1"),
            site("formal", "sec-foo#0", "2"),
            site("permanent-future", "sec-foo#0", "3"),
            site("permanent-provenance", "sec-foo#0", "4"),
            site("definition", "sec-foo#0", "5"),
            site("formal", def, "1"),
            site("open", "sec-foo#0", "6"),
        ]
    );
}

#[test]
fn macro_uses_pass_variables_to_an_expansion() {
    let html = r#"<emu-clause id="sec-ifabruptm" aoid="IfAbruptM">
  <h1>IfAbruptM ( _value_, _capability_ )</h1>
  <p>IfAbruptM is a shorthand for a sequence of algorithm steps. An algorithm step of the form:</p>
  <emu-alg>
    1. IfAbruptM(_value_, _capability_).
  </emu-alg>
  <p>means the same thing as:</p>
  <emu-alg>
    1. If _value_ is an abrupt completion, return _capability_.
    1. Set _value_ to ! _value_.
  </emu-alg>
</emu-clause>
<emu-clause id="sec-a" type="abstract operation">
  <h1>A ( _x_: an ECMAScript language value, ): an ECMAScript language value</h1>
  <dl class="header"></dl>
  <emu-alg>
    1. IfAbruptM(_x_, _x_).
    1. IfAbruptM(_x_, *true*).
    1. Return _x_.
  </emu-alg>
</emu-clause>
"#;
    let sp = crate::spec::scan(html).unwrap();
    let dt = build(html);
    let errs = crate::checks::macro_uses(&sp, &dt);
    assert_eq!(errs.len(), 1, "{errs:?}");
    assert!(errs[0].starts_with("sec-a #0: macro sec-ifabruptm: an argument that is not a variable"), "{errs:?}");
}

/// Abstract operations from (h1, steps), each its own clause `sec-<k>`.
fn aos(ops: &[(&str, &str)]) -> String {
    ops.iter()
        .enumerate()
        .map(|(k, (h1, steps))| format!("<emu-clause id=\"sec-{k}\" type=\"abstract operation\">\n  <h1>{h1}</h1>\n  <dl class=\"header\"></dl>\n  <emu-alg>\n{steps}\n  </emu-alg>\n</emu-clause>\n"))
        .collect()
}

/// `spec-gen types`' lines on abstract operations, without the header.
fn type_findings(ops: &[(&str, &str)]) -> Vec<String> {
    let html = aos(ops);
    let g = grammar();
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    crate::types::check(&sp, &g, &dt).0.iter().map(|f| f.line().trim_end().to_string()).collect()
}

const BAR: (&str, &str) = ("Bar ( _x_: a Boolean, ): a Number", "    1. If _x_ is *true*, return *1*<sub>𝔽</sub>.\n    1. Return *0*<sub>𝔽</sub>.");
const MAYBE: (&str, &str) = ("Maybe ( ): either a normal completion containing a Boolean or a throw completion", "    1. Return *true*.");

#[test]
fn types_an_argument_against_its_parameter() {
    let f = type_findings(&[BAR, ("Foo ( ): a Number", "    1. Return Bar(*\"a\"*).")]);
    assert_eq!(f, ["arg\tsec-1#0\t1\tBar argument 1 (_x_): String for Boolean"]);
    assert!(type_findings(&[BAR, ("Foo ( ): a Number", "    1. Return Bar(*false*).")]).is_empty());
}

#[test]
fn types_the_argument_count() {
    let f = type_findings(&[BAR, ("Foo ( ): a Number", "    1. Return Bar(*true*, *true*).")]);
    assert_eq!(f, ["arity\tsec-1#0\t1\tBar: 2 arguments for 1 parameters"]);
}

#[test]
fn types_a_return_against_the_header() {
    let f = type_findings(&[("Foo ( ): a Boolean", "    1. If *true* is *true*, return *undefined*.\n    1. Return *false*.")]);
    assert_eq!(f, ["return\tsec-0#0\t1\tundefined for Boolean"]);
    // a value returned where the header names completions is a normal completion
    assert!(type_findings(&[MAYBE]).is_empty());
}

#[test]
fn a_completion_used_as_a_value_is_unchecked() {
    let f = type_findings(&[BAR, MAYBE, ("Foo ( ): a Number", "    1. Return Bar(Maybe()).")]);
    assert_eq!(f, ["unchecked\tsec-2#0\t1\tBar argument 1 (_x_): normal completion of Boolean or abrupt completion for Boolean"]);
    assert!(type_findings(&[BAR, MAYBE, ("Foo ( ): either a normal completion containing a Number or a throw completion", "    1. Return Bar(? Maybe()).")]).is_empty());
}

#[test]
fn arithmetic_takes_operands_of_one_kind() {
    let f = type_findings(&[("Foo ( _n_: a Number, ): a Number", "    1. Let _m_ be _n_ + 1.\n    1. Return _n_ + _n_.")]);
    assert_eq!(f, ["operand\tsec-0#0\t1\tAdd: Number and mathematical value"]);
    let f = type_findings(&[("Foo ( _n_: a Number, ): a Boolean", "    1. If _n_ &lt; 1, return *true*.\n    1. Return *false*.")]);
    assert_eq!(f, ["operand\tsec-0#0\t1\t<: Number and mathematical value"]);
}

#[test]
fn a_variable_has_every_sort_bound_to_it() {
    // _v_ is a Number or a mathematical value, which meets the operand 1
    let f = type_findings(&[("Foo ( _n_: a Number, ): a Number", "    1. Let _v_ be _n_.\n    1. Set _v_ to 2.\n    1. Let _w_ be _v_ + 1.\n    1. Return _n_.")]);
    assert!(f.is_empty(), "{f:?}");
}

#[test]
fn a_loop_runs_over_a_list() {
    let f = type_findings(&[("Foo ( _s_: a String, ): ~unused~", "    1. For each element _e_ of _s_, do\n      1. Perform Foo(_e_).\n    1. Return ~unused~.")]);
    assert_eq!(f, ["base\tsec-0#0\t1\ta loop over String"]);
}

#[test]
fn a_closure_returns_by_its_own_type() {
    let f = type_findings(&[("Foo ( ): an Abstract Closure", "    1. Let _c_ be a new Abstract Closure with no parameters that captures nothing and performs the following steps when called:\n      1. Return *undefined*.\n    1. Return _c_.")]);
    assert!(f.is_empty(), "{f:?}");
}

#[test]
fn esmeta_names_name_operations_and_rows() {
    let n = crate::types::esmeta_names(r#"["DoWait", "FunctionBody[0,0].EvaluateFunctionBody", "Record[SourceTextModuleRecord].ExecuteModule"]"#);
    assert_eq!(n, ["DoWait", "FunctionBody[0,0].EvaluateFunctionBody", "Record[SourceTextModuleRecord].ExecuteModule"]);
    assert!(crate::types::esmeta_names_alg("DoWait", "DoWait", None));
    assert!(crate::types::esmeta_names_alg(&n[1], "EvaluateFunctionBody", Some("FunctionBody : FunctionStatementList")));
    assert!(!crate::types::esmeta_names_alg(&n[1], "EvaluateFunctionBody", Some("ConciseBody : ExpressionBody")));
    assert!(crate::types::esmeta_names_alg(&n[2], "ExecuteModule", None));
}

#[test]
fn a_check_of_a_value_never_a_completion() {
    let f = type_findings(&[BAR, ("Foo ( ): a Number", "    1. Return ! Bar(*true*).")]);
    assert_eq!(f, ["check\tsec-1#0\t1\t! of Number, never a completion"]);
}

#[test]
fn a_variable_read_but_never_bound() {
    let f = type_findings(&[("Foo ( ): a Number", "    1. Return _y_.")]);
    assert_eq!(f, ["unbound\tsec-0#0\t1\t_y_ is read but never bound"]);
}

#[test]
fn an_annex_row_takes_the_parameters_of_the_sdo_it_extends() {
    let sdo = "<emu-clause id=\"sec-f\" type=\"sdo\">\n<h1>Runtime Semantics: F ( _r_: a Record, _d_: ~forward~ or ~backward~, ): a Number</h1>\n</emu-clause>\n";
    let sp = crate::spec::scan(sdo).unwrap();
    let names = |lead: &str| crate::header::extended_params(lead, &sp.clauses).map(|ps| ps.into_iter().map(|p| p.name).collect::<Vec<_>>());
    assert_eq!(names("<p>The semantics of F with arguments _r_ and _d_ is extended as follows:</p><p>Rules are added:</p>"), Ok(vec!["r".to_string(), "d".to_string()]));
    assert_eq!(names("<p>The semantics of G is extended as follows:</p>"), Ok(vec![]));
    assert!(names("<p>The semantics of F with argument _r_ is extended as follows:</p>").is_err());
}

/// Declarations with a small sort hierarchy: function object, constructor and Proxy exotic object below
/// Object; Cyclic Module Record a Record kind below Module Record.
fn ty_decls() -> crate::decls::Decls {
    let mut d = crate::decls::Decls::default();
    for (s, sup, record) in [("Object", None, false), ("function object", Some("Object"), false), ("constructor", Some("function object"), false), ("Proxy exotic object", Some("Object"), false), ("Module Record", None, true), ("Cyclic Module Record", Some("Module Record"), true)] {
        let id = d.sorts.intern(s);
        let sup: Vec<usize> = sup.map(|x| d.sorts.intern(x)).into_iter().collect();
        if d.sort_defs.len() <= id {
            d.sort_defs.resize(id + 1, None);
        }
        if s != "Object" {
            d.sort_defs[id] = Some(crate::decls::SortDef { sup, test: None, record, ctx: None });
        }
    }
    d
}

#[test]
fn types_are_tag_disjoint_unions() {
    use crate::tylang::{sort_t, Hier, T};
    let d = ty_decls();
    let h = Hier::new(&d);
    let s = |n: &str| d.sorts.get(n).unwrap();
    // members of one tag merge: Int within Math, Object bounds in common
    assert_eq!(T::union(&h, [T::Int, T::Math, T::Inf]).show(&d), "ExtMath");
    let ctor = sort_t(&d, &h, s("constructor"));
    let fun = sort_t(&d, &h, s("function object"));
    assert_eq!(ctor.show(&d), "Object<constructor>");
    assert_eq!(ctor.join(&h, &fun), fun);
    assert!(ctor.sub(&h, &fun) && !fun.sub(&h, &ctor) && fun.sub(&h, &T::obj(None)));
    // two bounds sharing only the root join to any Object
    let j = fun.join(&h, &sort_t(&d, &h, s("Proxy exotic object")));
    assert_eq!(j, T::obj(None));
    assert!(T::obj(None).sub(&h, &j) && j.sub(&h, &T::obj(None)));
    // Record kinds are tags: a kind below another goes
    let (m, c) = (sort_t(&d, &h, s("Module Record")), sort_t(&d, &h, s("Cyclic Module Record")));
    assert_eq!(c.join(&h, &m), m);
    assert_eq!(T::union(&h, [c.clone(), T::Undefined]).show(&d), "Undefined | Rec<Cyclic Module Record>");
    // the named unions print by name
    assert_eq!(T::opt(&h, T::lang()).show(&d), "Opt<LangValue>");
    assert_eq!(T::completion(&h, T::Bool).show(&d), "Completion<Bool>");
    assert_eq!(T::union(&h, [T::lang(), T::Any]), T::Any);
}

#[test]
fn types_order_by_inclusion() {
    use crate::tylang::{Hier, T};
    let d = ty_decls();
    let h = Hier::new(&d);
    let l = |t: T| T::List(Box::new(t));
    // List is invariant; Normal covariant; a closure's parameters contravariant
    assert!(!l(T::Int).sub(&h, &l(T::Math)) && l(T::Int).sub(&h, &l(T::Int)) && l(T::Int).sub(&h, &l(T::Any)));
    assert!(T::Normal(Box::new(T::Int)).sub(&h, &T::completion(&h, T::Math)));
    let f = |p: T, r: T| T::Closure(Some((vec![p], Box::new(r))));
    assert!(f(T::Math, T::Int).sub(&h, &f(T::Int, T::Math)) && !f(T::Int, T::Int).sub(&h, &f(T::Math, T::Int)));
    assert!(T::never().sub(&h, &T::Bool) && !T::Any.sub(&h, &T::Bool));
    // "is present" narrows Opt<T> to T
    let o = T::opt(&h, T::lang());
    assert_eq!(o.without(&h, &T::Absent), T::lang());
    assert_eq!(o.within(&h, &T::union(&h, [T::String, T::Symbol])).show(&d), "String | Symbol");
    assert!(o.meets(&h, &T::Absent) && !T::lang().meets(&h, &T::Absent));
}

#[test]
fn narrowing_meets_member_by_member() {
    use crate::tylang::{sort_t, Hier, T};
    let mut d = ty_decls();
    let (a, b, c) = (d.enums.intern("a"), d.enums.intern("b"), d.enums.intern("c"));
    let h = Hier::new(&d);
    let s = |n: &str| d.sorts.get(n).unwrap();
    // IsCallable narrows a language value to the Callable marker
    let fun = sort_t(&d, &h, s("function object"));
    assert_eq!(T::lang().within(&h, &fun), fun);
    assert_eq!(T::opt(&h, T::lang()).within(&h, &fun).show(&d), "Object<function object>");
    let px = sort_t(&d, &h, s("Proxy exotic object"));
    assert_eq!(px.within(&h, &fun).show(&d), "Object<function object + Proxy exotic object>");
    assert_eq!(T::Math.within(&h, &T::Int), T::Int);
    assert_eq!(T::ext_math(&h).within(&h, &T::Int), T::Int);
    let m = sort_t(&d, &h, s("Module Record"));
    assert_eq!(T::Rec(None).within(&h, &m), m);
    let e = |xs: &[usize]| T::Enum(xs.iter().copied().collect());
    assert_eq!(e(&[a, b]).within(&h, &e(&[b, c])), e(&[b]));
    assert_eq!(T::Enum(Default::default()).within(&h, &e(&[c])), e(&[c]));
    assert_eq!(T::completion(&h, T::Math).within(&h, &T::Normal(Box::new(T::Int))), T::Normal(Box::new(T::Int)));
    assert_eq!(T::Bool.within(&h, &T::Int), T::never());
}

#[test]
fn a_builtin_parameter_is_a_language_value_or_absent() {
    let html = format!(
        "{}<emu-clause id=\"sec-foo.bar\" type=\"built-in function\">\n  <h1>Foo.bar ( _x_ )</h1>\n  <p>This function performs the following steps when called:</p>\n  <emu-alg>\n    1. Perform Baz(_x_).\n    1. Return *undefined*.\n  </emu-alg>\n</emu-clause>\n",
        aos(&[("Baz ( _l_: a List of Strings, ): ~unused~", "    1. Return ~unused~.")])
    );
    let g = grammar();
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    let f: Vec<String> = crate::types::check(&sp, &g, &dt).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    assert_eq!(f.len(), 1, "{f:?}");
    assert!(f[0].starts_with("arg\tsec-foo.bar#0\t1\tBaz argument 1 (_l_): undefined or ") && f[0].ends_with("Object or absent for List"), "{f:?}");
}

#[test]
fn a_parenthesized_expression_is_typed() {
    let f = type_findings(&[BAR, ("Foo ( ): a Number", "    1. Return (Bar(*\"a\"*)).")]);
    assert_eq!(f, ["arg\tsec-1#0\t1\tBar argument 1 (_x_): String for Boolean"]);
}

/// A grammar over one overlay file `emu`, in the fresh directory `name`.
fn overlay_grammar(name: &str, emu: &str) -> Grammar {
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join(name);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("o.emu"), emu).unwrap();
    Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap()
}

/// `spec-gen types`' lines and the result typings' on abstract operations, under the grammar `g`.
fn type_findings_in(g: &Grammar, ops: &[(&str, &str)]) -> Vec<String> {
    let html = aos(ops);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, g);
    let mut dt = crate::data::build(&html, &sp, g, &rows);
    let ts = crate::tables::build(&html, &sp, g, &mut dt);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let mut fs = crate::types::check(&sp, g, &dt).0;
    fs.extend(crate::types::typings(&sp, g, &dt, &td));
    fs.iter().map(|f| f.line().trim_end().to_string()).collect()
}

#[test]
fn a_primitive_signature_is_read_as_a_header_type() {
    let g = overlay_grammar(
        "spec-gen-prim-sig",
        r#"<emu-clause id="formal-x">
  <emu-primitive id="prim-foo" name="Foo">
    <emu-signature>Foo(_x_: a List of Numbers or ~empty~): a List of Strings or ~empty~</emu-signature>
    <p>f</p>
  </emu-primitive>
</emu-clause>
"#,
    );
    let f = type_findings_in(&g, &[("Bar ( ): a Number", "    1. Return Foo(*true*).")]);
    assert_eq!(f, ["arg\tsec-0#0\t1\tFoo argument 1: Boolean for List or ~empty~", "return\tsec-0#0\t1\tList or ~empty~ for Number"]);
    assert_eq!(crate::sig::res(&g, "SourceText").as_deref(), Some("a List of code points"));
}

#[test]
fn a_result_type_narrows_the_operations_result() {
    let g = overlay_grammar(
        "spec-gen-result-type",
        r#"<emu-clause id="formal-x">
  <emu-result-type clause="sec-0">a Boolean</emu-result-type>
  <emu-result-type clause="sec-2">a String</emu-result-type>
</emu-clause>
"#,
    );
    let baz = ("Baz ( ): either a Boolean or a Number", "    1. Return *true*.");
    let f = type_findings_in(&g, &[baz, ("Foo ( ): a Number", "    1. Return Baz()."), ("Qux ( ): a Boolean", "    1. Return *\"a\"*.")]);
    assert_eq!(f, ["return\tsec-1#0\t1\tBoolean for Number", "typing\tsec-2\t\tresult String not within the header's Bool"]);
}

#[test]
fn a_return_outside_the_result_typing_is_a_finding() {
    let g = overlay_grammar(
        "spec-gen-result-type-return",
        r#"<emu-clause id="formal-x">
  <emu-phrase id="ph-elem-whose-tn" kind="expression" rule="elem-whose-tn" alternatives="all">
    <emu-pattern>the _t_ in _l_ whose _f_ is _v_</emu-pattern>
    <p>"field" only says that it names a field.</p>
    <emu-params>_t_: a type, _l_: a List, _f_: a field name, _v_: anything</emu-params>
    <emu-alg>
      1. Return _v_.
    </emu-alg>
  </emu-phrase>
  <emu-sort name="Reference Record" record clause="sec-0"></emu-sort>
  <emu-sort name="Private Name" record clause="sec-0"></emu-sort>
  <emu-result-type clause="ph-elem-whose-tn">a _t_</emu-result-type>
  <emu-result-type clause="sec-0">either a Boolean or a Reference Record</emu-result-type>
  <emu-result-type clause="sec-1">either a Boolean or a Private Name</emu-result-type>
</emu-clause>
"#,
    );
    let steps = "    1. Let _p_ be the Private Name in _l_ whose [[Description]] is *\"x\"*.\n    1. Return _p_.";
    let f = type_findings_in(&g, &[("Foo ( _l_: a List ): either a Boolean, a Reference Record, or a Private Name", steps), ("Bar ( _l_: a List ): either a Boolean, a Reference Record, or a Private Name", steps)]);
    assert_eq!(f, ["typing\tsec-0#0\t2\ta return: Rec<Private Name> not within the typing Bool | Rec<Reference Record>"]);
}

#[test]
fn a_bad_result_type_is_an_anchor_error() {
    let g = overlay_grammar(
        "spec-gen-result-type-bad",
        r#"<emu-clause id="formal-x">
  <emu-result-type clause="sec-0">a Boolean, as it were</emu-result-type>
</emu-clause>
"#,
    );
    let html = aos(&[("Foo ( ): a Boolean", "    1. Return *true*.")]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(&html, &sp, &g, &rows);
    assert_eq!(dt.anchor_errors, ["o.emu: <emu-result-type clause=sec-0>: \"a Boolean, as it were\" is not a header type"]);
    assert!(dt.algs[0].hdr.typing.is_none());
}

#[test]
fn a_negation_is_a_number_bigint_or_mathematical_value() {
    let f = type_findings_in(&grammar(), &[("Foo ( _x_: a Number ): a BigInt", "    1. Return the negative of _x_."), ("Bar ( _x_: a Number ): a String", "    1. Return the negative of _x_.")]);
    assert_eq!(f, ["return\tsec-1#0\t1\tNumber or BigInt or mathematical value or ±∞ for String"]);
}

#[test]
fn a_type_phrase_is_bounded_by_its_test() {
    let g = overlay_grammar(
        "spec-gen-type-bound",
        r#"<emu-clause id="formal-x">
  <emu-phrase id="ph-type-but-not-one" kind="type" subject="_v_" rule="ht-but-not-one">
    <emu-pattern>_t_, but not _u_</emu-pattern>
    <emu-params>_t_: a type, _u_: a type, _v_: anything</emu-params>
    <emu-alg>
      1. If _v_ is not a _t_, return *false*.
      1. If _v_ is a _u_, return *false*.
      1. Return *true*.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#,
    );
    let f = type_findings_in(&g, &[("Baz ( _x_: a String, but not a Number ): a Boolean", "    1. Return *true*."), ("Foo ( ): a Boolean", "    1. Return Baz(*true*).")]);
    assert_eq!(f, ["arg\tsec-1#0\t1\tBaz argument 1 (_x_): Boolean for String"]);
}

/// The declarations and data of `html`: (spec, grammar, data, declarations).
fn ty_data(html: &str) -> (crate::spec::Spec, Grammar, crate::data::Data, crate::tydecls::TyDecls) {
    let g = grammar();
    let sp = crate::spec::scan(html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(html, &sp, &g, &rows);
    let ts = crate::tables::build_with(html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    (sp, g, dt, td)
}

#[test]
fn the_sound_mode_accepts_only_a_type_within() {
    let html = aos(&[
        ("Baz ( _o_: an Object ): a Boolean", "    1. Return *true*."),
        ("Foo ( _x_: an ECMAScript language value ): a Boolean", "    1. Return Baz(_x_)."),
        ("Qux ( _x_ ): a Boolean", "    1. Return Baz(_x_)."),
        ("Int ( _n_: an integer ): a Boolean", "    1. Return *true*."),
        ("Mv ( _m_: a mathematical value ): a Boolean", "    1. If Int(_m_) is *true*, return Int(3).\n    1. Return Baz(*undefined*)."),
    ]);
    let (sp, g, dt, td) = ty_data(&html);
    let (fs, n, _) = crate::types::within(&sp, &g, &dt, &td);
    let f: Vec<String> = fs.iter().map(|f| f.line().trim_end().to_string()).collect();
    assert_eq!(
        f,
        [
            "meets\tsec-1#0\t1\tBaz argument 1 (_o_): LangValue for Object",
            "unknown\tsec-2#0\t1\tBaz argument 1 (_o_): Any for Object",
            "meets\tsec-4#0\t1\tInt argument 1 (_n_): Math for Int",
            "disjoint\tsec-4#0\t2\tBaz argument 1 (_o_): Undefined for Object",
        ]
    );
    // arguments: Int(3) within; returns: four Booleans within
    assert_eq!(n[0], [1, 2, 1, 1]);
    assert_eq!(n[1], [6, 0, 0, 0]);
}

#[test]
fn a_method_clause_is_checked_against_its_trait() {
    let table = r#"<emu-table id="table-essential-internal-methods" caption="Essential Internal Methods" type="internal methods" of="all objects">
  <table>
    <thead>
      <tr><th>Internal Method</th><th>Description</th><th>Definitions</th></tr>
    </thead>
    <tr><td>[[IsExtensible]] ( ): either a normal completion containing a Boolean or a throw completion</td><td>d</td><td>d</td></tr>
    <tr>
      <td>
        [[SetPrototypeOf]] (
          _proto_: an Object or *null*,
        ): either a normal completion containing a Boolean or a throw completion
      </td>
      <td>d</td>
      <td>d</td>
    </tr>
  </table>
</emu-table>
"#;
    let clause = |id: &str, h1: &str, ret: &str| format!("<emu-clause id=\"{id}\" type=\"internal method\">\n  <h1>{h1}</h1>\n  <dl class=\"header\">\n    <dt>for</dt>\n    <dd>an Object _O_</dd>\n  </dl>\n  <emu-alg>\n    1. Return {ret}.\n  </emu-alg>\n</emu-clause>\n");
    let html = format!(
        "{table}{}{}{}",
        clause("sec-a", "[[IsExtensible]] ( ): a normal completion containing a String", "*\"x\"*"),
        clause("sec-b", "[[SetPrototypeOf]] ( _V_: an Object ): a normal completion containing a Boolean", "*true*"),
        clause("sec-c", "[[IsExtensible]] ( ): a normal completion containing *false*", "*false*"),
    );
    let (sp, _, dt, td) = ty_data(&html);
    let (fs, n) = crate::types::impls(&sp, &dt, &td);
    let f: Vec<String> = fs.iter().map(|f| f.line().trim_end().to_string()).collect();
    assert_eq!(
        f,
        [
            "impl\tsec-a#0\t\t[[IsExtensible]]: result Normal<String> not within Object's Completion<Bool>",
            "impl\tsec-b#0\t\t[[SetPrototypeOf]] parameter 1 (_V_): Object's Null | Object not within Object",
        ]
    );
    assert_eq!(n, [3, 0, 0]);
}

/// The sound mode's findings on abstract operations, as lines.
fn within_lines(ops: &[(&str, &str)]) -> Vec<String> {
    let (sp, g, dt, td) = ty_data(&aos(ops));
    crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect()
}

const BAZ: (&str, &str) = ("Baz ( _o_: an Object ): a Boolean", "    1. Return *true*.");

#[test]
fn narrowing_follows_the_path() {
    let f = within_lines(&[
        BAZ,
        ("Obj ( ): an Object", "    1. Return %Object.prototype%."),
        ("Exit ( _x_: an ECMAScript language value ): a Boolean", "    1. If _x_ is not an Object, throw a *TypeError* exception.\n    1. Return Baz(_x_)."),
        (
            "Join ( _x_: an ECMAScript language value ): a Boolean",
            "    1. If _x_ is *undefined*, then\n      1. Set _x_ to Obj().\n    1. Else if _x_ is not an Object, then\n      1. Throw a *TypeError* exception.\n    1. Return Baz(_x_).",
        ),
        (
            "Loop ( _x_: an ECMAScript language value, _l_: a List of Strings ): a Boolean",
            "    1. If _x_ is not an Object, throw a *TypeError* exception.\n    1. For each element _e_ of _l_, do\n      1. Perform Baz(_x_).\n    1. Return *true*.",
        ),
        (
            "Drop ( _x_: an ECMAScript language value, _l_: a List of Strings ): a Boolean",
            "    1. If _x_ is not an Object, throw a *TypeError* exception.\n    1. For each element _e_ of _l_, do\n      1. Perform Baz(_x_).\n      1. Set _x_ to *undefined*.\n    1. Return *true*.",
        ),
        ("Either ( _x_: an ECMAScript language value ): a Boolean", "    1. If _x_ is an Object, then\n      1. Perform Baz(_x_).\n    1. Return Baz(_x_)."),
    ]);
    // the loop head keeps _x_'s narrowing when the body never assigns it; a branch's ends join
    assert_eq!(
        f,
        [
            "meets\tsec-5#0\t2.a\tBaz argument 1 (_o_): LangValue for Object",
            "meets\tsec-6#0\t2\tBaz argument 1 (_o_): LangValue for Object",
        ]
    );
}

#[test]
fn guards_presence_and_exits_narrow() {
    let f = within_lines(&[
        BAZ,
        ("IsCallable ( _argument_: an ECMAScript language value ): a Boolean", "    1. Return *true*."),
        ("Fn ( _f_: a function object ): a Boolean", "    1. Return *true*."),
        ("Str ( _s_: a String ): a Boolean", "    1. Return *true*."),
        ("Call ( _f_: an ECMAScript language value ): a Boolean", "    1. If IsCallable(_f_) is *false*, throw a *TypeError* exception.\n    1. Return Fn(_f_)."),
        ("Pres ( optional _s_: a String ): a Boolean", "    1. If _s_ is present, return Str(_s_).\n    1. Return Str(_s_)."),
        ("Raw ( optional _s_: a String ): a Boolean", "    1. Return Str(_s_)."),
        ("Req ( _o_: an ECMAScript language value ): either a normal completion containing ~unused~ or a throw completion", "    1. If _o_ is not an Object, throw a *TypeError* exception.\n    1. Return ~unused~."),
        ("Use ( _v_: an ECMAScript language value ): either a normal completion containing a Boolean or a throw completion", "    1. Perform ? Req(_v_).\n    1. Return Baz(_v_)."),
    ]);
    // an AO's parameter not passed is absent, not *undefined*
    assert_eq!(f, ["disjoint\tsec-5#0\t2\tStr argument 1 (_s_): Absent for String", "meets\tsec-6#0\t1\tStr argument 1 (_s_): Opt<String> for String"]);
}

#[test]
fn list_elements_come_from_their_adds_and_uses() {
    let f = within_lines(&[
        ("Names ( ): a List of Strings", "    1. Let _l_ be a new empty List.\n    1. Append *\"a\"* to _l_.\n    1. Return _l_."),
        ("Bad ( ): a List of Strings", "    1. Let _l_ be a new empty List.\n    1. Append *1*<sub>𝔽</sub> to _l_.\n    1. Return _l_."),
        ("Lit ( ): a List of Strings", "    1. Return « *\"a\"*, *\"b\"* »."),
        ("Len ( _l_: a List of ECMAScript language values ): a Boolean", "    1. If _l_ is empty, return *true*.\n    1. Return *false*."),
        ("Ro ( _s_: a List of Strings ): a Boolean", "    1. Return Len(_s_)."),
        ("Push ( _l_: a List of ECMAScript language values ): ~unused~", "    1. Append *undefined* to _l_.\n    1. Return ~unused~."),
        ("Rw ( _s_: a List of Strings ): ~unused~", "    1. Return Push(_s_)."),
        ("Add ( _s_: a List of Strings ): ~unused~", "    1. Append *undefined* to _s_.\n    1. Return ~unused~."),
    ]);
    // a callee that only reads its List takes a List of narrower elements; one that adds to it does not
    assert_eq!(
        f,
        [
            "meets\tsec-1#0\t3\ta return: List<String | Number> for List<String>",
            "meets\tsec-6#0\t1\tPush argument 1 (_l_): List<String> for List<LangValue>",
            "disjoint\tsec-7#0\t1\tan element added by append: Undefined for String",
        ]
    );
}

#[test]
fn prose_fields_opaque_sorts_and_guards_are_declared() {
    use crate::overlay::{Fields, Guard, Overlay, Sort, SortTest};
    use crate::tylang::T;
    let mut o = Overlay::default();
    o.sorts.push(Sort { name: "Data Block".into(), sup: None, record: false, test: SortTest::None, clause: String::new(), context: None, ty: Some("a List of Numbers".into()) });
    let rows = [("DateValue", "a Number"), ("Buf", "a Data Block"), ("Odd", "a frobnicated thing")];
    o.fields.push(Fields { of: "Date instance".into(), slots: true, rows: rows.iter().map(|(f, t)| (f.to_string(), t.to_string())).collect() });
    o.guards.push(Guard { op: "IsFoo".into(), ty: "a String".into() });
    let g = Grammar::new(o).unwrap();
    let html = aos(&[("Foo ( ): a Boolean", "    1. Return *true*.")]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(&html, &sp, &g, &rows);
    let ts = crate::tables::build_with(&html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let d = &dt.decls;
    let block = d.sorts.get("Data Block").unwrap();
    assert_eq!(crate::tylang::sort_t(d, &td.hier, block), T::List(Box::new(T::Number)));
    let s = td.shapes.iter().find(|s| s.name == "Date instance").unwrap();
    let fs: Vec<(String, String)> = s.fields.iter().map(|(f, t)| (d.fields.name(*f).to_string(), t.show(d))).collect();
    assert_eq!(fs, [("DateValue".into(), "Number".into()), ("Buf".into(), "List<Number>".into()), ("Odd".into(), "Any".into())]);
    assert_eq!(s.dynamic.iter().map(|x| x.1.as_str()).collect::<Vec<_>>(), ["a frobnicated thing"]);
    assert!(s.slots);
    assert_eq!(td.guards, [("IsFoo".to_string(), T::String)]);
}

/// A built-in function's clause: its id, its header and its steps.
fn builtin_fn(id: &str, h1: &str, steps: &str) -> String {
    format!("<emu-clause id=\"{id}\" type=\"built-in function\">\n  <h1>{h1}</h1>\n  <p>This function performs the following steps when called:</p>\n  <emu-alg>\n{steps}\n  </emu-alg>\n</emu-clause>\n")
}

#[test]
fn a_builtins_parameter_not_passed_reads_as_undefined() {
    let html = aos(&[BAZ, ("Str ( _s_: a String ): a Boolean", "    1. Return *true*."), ("Lv ( _v_: an ECMAScript language value ): a Boolean", "    1. Return *true*.")])
        + &builtin_fn("sec-foo.a", "Foo.a ( _x_ )", "    1. Perform Lv(_x_).\n    1. If _x_ is not present, return Str(_x_).\n    1. If _x_ is *undefined*, return Baz(_x_).\n    1. If _x_ is not an Object, return *false*.\n    1. Return Baz(_x_).")
        + &builtin_fn("sec-foo.b", "Foo.b ( _x_ )", "    1. Let _y_ be _x_.\n    1. If _y_ is present, return Lv(_y_).\n    1. Return Str(_y_).");
    let (sp, g, dt, td) = ty_data(&html);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    // a use reads it as *undefined*; `is present` alone sees it; a copy keeps it not present
    assert_eq!(
        f,
        [
            "disjoint\tsec-foo.a#0\t2\tStr argument 1 (_s_): Undefined for String",
            "disjoint\tsec-foo.a#0\t3\tBaz argument 1 (_o_): Undefined for Object",
            "disjoint\tsec-foo.b#0\t3\tStr argument 1 (_s_): Undefined for String",
        ]
    );
}

#[test]
fn an_anonymous_records_field_is_no_tables() {
    let table = "<emu-table id=\"table-foo-record\" caption=\"Foo Record Fields\">\n  <table>\n    <tr><th>Field Name</th><th>Value</th><th>Meaning</th></tr>\n    <tr><td>[[Elements]]</td><td>a List of Strings</td><td>m</td></tr>\n  </table>\n</emu-table>\n";
    let html = table.to_string()
        + &aos(&[
            ("Str ( _s_: a String ): a Boolean", "    1. Return *true*."),
            ("Grp ( ): a Boolean", "    1. Let _g_ be the Record { [[Key]]: *\"k\"*, [[Elements]]: « *1*<sub>𝔽</sub> » }.\n    1. For each element _e_ of _g_.[[Elements]], do\n      1. Perform Str(_e_).\n    1. Return *true*."),
        ]);
    let (sp, g, dt, td) = ty_data(&html);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    assert_eq!(f, ["unknown\tsec-1#0\t2\ta loop over: Any for List<Any>", "unknown\tsec-1#0\t2.a\tStr argument 1 (_s_): Any for String"]);
}

#[test]
fn an_add_through_a_shared_list_is_checked() {
    let f = within_lines(&[
        ("Names ( ): a List of Strings", "    1. Let _l_ be a new empty List.\n    1. Append *\"a\"* to _l_.\n    1. Return _l_."),
        ("AliasAdd ( _s_: a List of Strings ): ~unused~", "    1. Let _l_ be _s_.\n    1. Append *undefined* to _l_.\n    1. Return ~unused~."),
        ("CallAdd ( ): ~unused~", "    1. Let _l_ be Names().\n    1. Append *undefined* to _l_.\n    1. Return ~unused~."),
        ("Own ( ): ~unused~", "    1. Let _l_ be a new empty List.\n    1. Let _m_ be _l_.\n    1. Append *undefined* to _m_.\n    1. Return Len(_l_)."),
        ("Len ( _l_: a List of Strings ): ~unused~", "    1. Return ~unused~."),
    ]);
    // a List made elsewhere keeps its elements' type; an add through an alias of a new List leaves its elements unknown
    assert_eq!(
        f,
        [
            "disjoint\tsec-1#0\t2\tan element added by append: Undefined for String",
            "disjoint\tsec-2#0\t2\tan element added by append: Undefined for String",
            "meets\tsec-3#0\t4\tLen argument 1 (_l_): List<Any> for List<String>",
        ]
    );
}

#[test]
fn a_loop_that_sets_a_completions_field_drops_its_narrowing() {
    let f = within_lines(&[
        BAZ,
        (
            "Nf ( _c_: either a normal completion containing an Object or a throw completion, _l_: a List of Strings ): a Boolean",
            "    1. If _c_ is an abrupt completion, return *false*.\n    1. Perform Baz(_c_.[[Value]]).\n    1. For each element _e_ of _l_, do\n      1. Perform Baz(_c_.[[Value]]).\n      1. Set _c_.[[Value]] to *undefined*.\n    1. Return *true*.",
        ),
    ]);
    assert_eq!(f, ["unknown\tsec-1#0\t3.a\tBaz argument 1 (_o_): Any for Object", "disjoint\tsec-1#0\t3.b\ta value set in [[Value]]: Undefined for Object"]);
}

#[test]
fn a_slot_rebound_to_a_disjoint_type_is_versioned() {
    let ops = [
        ("Lv ( _v_: an ECMAScript language value ): a Boolean", "    1. Return *true*."),
        ("Bo ( _b_: a Boolean ): a Boolean", "    1. Return *true*."),
        MAYBE,
        ("ReturnIfAbrupt ( _x_: a Completion Record ): ~unused~", "    1. Return ~unused~."),
        ("Ver ( _x_: an ECMAScript language value ): a Boolean", "    1. Perform Lv(_x_).\n    1. Set _x_ to 3.\n    1. Repeat, while _x_ > 0,\n      1. Set _x_ to _x_ - 1.\n    1. Return Lv(_x_)."),
        ("Ria ( ): either a normal completion containing a Boolean or a throw completion", "    1. Let _r_ be Maybe().\n    1. ReturnIfAbrupt(_r_).\n    1. Return Bo(_r_)."),
    ];
    let (sp, g, dt, td) = ty_data(&aos(&ops));
    let (fs, _, v) = crate::types::within(&sp, &g, &dt, &td);
    let f: Vec<String> = fs.iter().map(|f| f.line().trim_end().to_string()).collect();
    // each version has its own type: the parameter's, then an integer's
    assert_eq!(f, ["disjoint\tsec-4#0\t4\tLv argument 1 (_v_): Int for LangValue"]);
    let slots: Vec<(String, String, usize)> = v.slots.iter().map(|((k, x), n)| (k.clone(), x.clone(), *n)).collect();
    assert_eq!(slots, [("sec-4#0".into(), "_x_".into(), 2), ("sec-5#0".into(), "_r_".into(), 2)]);
}

#[test]
fn a_phrase_algorithm_is_typed_by_its_returns() {
    let g = overlay_grammar(
        "spec-gen-phrase-returns",
        r#"<emu-clause id="formal-x">
  <emu-phrase id="ph-the-name-of" kind="expression">
    <emu-pattern>the name of _v_</emu-pattern>
    <emu-params>_v_: anything</emu-params>
    <emu-alg>
      1. If _v_ is *undefined*, throw a *TypeError* exception.
      1. Return *"name"*.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#,
    );
    let html = aos(&[
        ("Str ( _s_: a String ): a Boolean", "    1. Return *true*."),
        ("Foo ( _v_: an ECMAScript language value ): either a normal completion containing a Boolean or a throw completion", "    1. Let _s_ be ? the name of _v_.\n    1. Return Str(_s_)."),
        ("Bar ( _v_: an ECMAScript language value ): a Boolean", "    1. Return Str(the name of _v_)."),
    ]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(&html, &sp, &g, &rows);
    let ts = crate::tables::build_with(&html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    // its throw makes it abrupt too, which `?` takes
    assert_eq!(f, ["meets\tsec-2#0\t1\tStr argument 1 (_s_): String | Abrupt for String"]);
}

#[test]
fn the_dyn_ratchet_counts_lines() {
    let (sp, g, dt, td) = ty_data(&aos(&[BAZ, ("Foo ( _x_: an ECMAScript language value ): a Boolean", "    1. Perform Baz(_x_).\n    1. Return Baz(_x_)."), ("Qux ( _x_ ): a Boolean", "    1. Return Baz(_x_).")]));
    let fs = crate::types::within(&sp, &g, &dt, &td).0;
    let ls = crate::types::dyn_lines(&fs);
    assert_eq!(ls[1], "# lines: 3; meets 2, unknown 1, disjoint 0\n");
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into()));
    let file = dir.join("type-dyn-sites.txt");
    std::fs::write(&file, ls.concat()).unwrap();
    assert_eq!(crate::types::check_file(&fs, file.to_str().unwrap()), Ok(true));
    std::fs::write(&file, ls[..ls.len() - 1].concat()).unwrap();
    assert_eq!(crate::types::check_file(&fs, file.to_str().unwrap()), Ok(false));
}

#[test]
fn a_field_of_an_unknown_base_is_any_and_a_field_write_is_checked() {
    let g = overlay_grammar(
        "spec-gen-field-write",
        r#"<emu-clause id="formal-x">
  <emu-sort name="Foo Record" record clause="sec-0"></emu-sort>
</emu-clause>
"#,
    );
    let table = "<emu-table id=\"table-foo-record\" caption=\"Foo Record Fields\">\n  <table>\n    <tr><th>Field Name</th><th>Value</th><th>Meaning</th></tr>\n    <tr><td>[[Key]]</td><td>a String</td><td>m</td></tr>\n    <tr><td>[[Elements]]</td><td>a List of Strings</td><td>m</td></tr>\n  </table>\n</emu-table>\n";
    let html = table.to_string()
        + &aos(&[
            ("Str ( _s_: a String ): a Boolean", "    1. Return *true*."),
            ("Mk ( _x_ ): a Boolean", "    1. Let _r_ be the Foo Record { [[Key]]: 1, [[Elements]]: « » }.\n    1. Set _r_.[[Key]] to _x_.\n    1. Set _r_.[[Elements]] to « *\"a\"* ».\n    1. Return Str(_r_.[[Key]])."),
            ("Rd ( _x_ ): a Boolean", "    1. Return Str(_x_.[[Key]])."),
            ("Cv ( _c_: a normal completion containing a String ): a Boolean", "    1. Set _c_.[[Value]] to *undefined*.\n    1. Return *true*."),
        ]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(&html, &sp, &g, &rows);
    let ts = crate::tables::build_with(&html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    // a known kind's field is checked where it is written; an unknown base's field is Any
    assert_eq!(
        f,
        [
            "disjoint\tsec-1#0\t1\t[[Key]] of a Foo Record literal: Int for String",
            "unknown\tsec-1#0\t2\ta value set in [[Key]]: Any for String",
            "unknown\tsec-2#0\t1\t[[Key]] of: Any for Object | Rec",
            "unknown\tsec-2#0\t1\tStr argument 1 (_s_): Any for String",
            "disjoint\tsec-3#0\t1\ta value set in [[Value]]: Undefined for String",
        ]
    );
}

#[test]
fn an_element_added_to_a_field_of_an_unknown_base_is_checked_at_every_kind() {
    let g = overlay_grammar(
        "spec-gen-field-add",
        FIELD_ADD_EMU,
    );
    let table = "<emu-table id=\"table-foo-record\" caption=\"Foo Record Fields\">\n  <table>\n    <tr><th>Field Name</th><th>Value</th><th>Meaning</th></tr>\n    <tr><td>[[Elements]]</td><td>a List of Strings</td><td>m</td></tr>\n  </table>\n</emu-table>\n";
    let html = table.to_string()
        + &aos(&[(
            "Add ( _x_ ): ~unused~",
            "    1. Append 1 to _x_.[[Elements]].\n    1. Append the elements of « 1 » to _x_.[[Elements]].\n    1. Set _x_.[[Elements]][0] to 1.\n    1. Append *\"a\"* to _x_.[[Elements]].\n    1. Return ~unused~.",
        )]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(&html, &sp, &g, &rows);
    let ts = crate::tables::build_with(&html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    // the List may be a Foo Record's [[Elements]], whose reads take its elements as Strings
    assert_eq!(
        f,
        [
            "meets\tsec-0#0\t1\tan element added by append: Int for each of String, or none",
            "unknown\tsec-0#0\t1\t[[Elements]] of: Any for Object | Rec",
            "meets\tsec-0#0\t2\tthe elements added by ph-append-elements: Int for each of String, or none",
            "unknown\tsec-0#0\t2\t[[Elements]] of: Any for Object | Rec",
            "unknown\tsec-0#0\t2\tph-append-elements argument 2 (_b_): Any for List<Any>",
            "meets\tsec-0#0\t3\tan element set in a List: Int for each of String, or none",
            "unknown\tsec-0#0\t3\tan index into: Any for List<Any>",
            "unknown\tsec-0#0\t3\t[[Elements]] of: Any for Object | Rec",
            "unknown\tsec-0#0\t4\t[[Elements]] of: Any for Object | Rec",
        ]
    );
}

/// A Record sort and lists.emu's ph-append-elements, for adds to a field's List.
const FIELD_ADD_EMU: &str = r#"<emu-clause id="formal-x">
  <emu-sort name="Foo Record" record clause="sec-0"></emu-sort>
  <emu-phrase id="ph-append-elements" kind="step">
    <emu-pattern>Append the elements of _a_ to _b_.</emu-pattern>
    <emu-params>_a_: a List, _b_: a List</emu-params>
    <emu-alg>
      1. For each element _e_ of _a_, do
        1. Append _e_ to _b_.
      1. Return ~unused~.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#;

#[test]
fn an_element_added_through_a_slot_bound_to_a_field_read_is_checked() {
    let g = overlay_grammar("spec-gen-alias-add", FIELD_ADD_EMU);
    let table = "<emu-table id=\"table-foo-record\" caption=\"Foo Record Fields\">\n  <table>\n    <tr><th>Field Name</th><th>Value</th><th>Meaning</th></tr>\n    <tr><td>[[Elements]]</td><td>a List of Strings</td><td>m</td></tr>\n  </table>\n</emu-table>\n";
    let html = table.to_string() + &aos(&[("Add ( _x_ ): ~unused~", "    1. Let _l_ be _x_.[[Elements]].\n    1. Append 1 to _l_.\n    1. Append *\"a\"* to _l_.\n    1. Return ~unused~.")]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(&html, &sp, &g, &rows);
    let ts = crate::tables::build_with(&html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    // _l_ is the List a Foo Record's [[Elements]] holds, of Strings
    assert_eq!(
        f,
        [
            "unknown\tsec-0#0\t1\t[[Elements]] of: Any for Object | Rec",
            "meets\tsec-0#0\t2\tan element added by append: Int for each of String, or none",
        ]
    );
}

#[test]
fn a_phrase_algorithms_arguments_are_checked() {
    let g = overlay_grammar(
        "spec-gen-phrase-args",
        r#"<emu-clause id="formal-x">
  <emu-phrase id="ph-the-name-of" kind="expression">
    <emu-pattern>the name of _v_</emu-pattern>
    <emu-params>_v_: a String</emu-params>
    <emu-alg>
      1. Return _v_.
    </emu-alg>
  </emu-phrase>
</emu-clause>
"#,
    );
    let html = aos(&[
        ("Str ( _s_: a String ): a Boolean", "    1. Return *true*."),
        ("Foo ( _v_: an ECMAScript language value ): a Boolean", "    1. Return Str(the name of _v_)."),
        ("Bar ( ): a Boolean", "    1. Return Str(the name of 3)."),
    ]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(&html, &sp, &g, &rows);
    let ts = crate::tables::build_with(&html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    assert_eq!(f, ["meets\tsec-1#0\t1\tph-the-name-of argument 1 (_v_): LangValue for String", "disjoint\tsec-2#0\t1\tph-the-name-of argument 1 (_v_): Int for String"]);
}

#[test]
fn an_exit_narrowing_keeps_a_parameter_not_passed() {
    let html = aos(&[
        ("Str ( _s_: a String ): a Boolean", "    1. Return *true*."),
        ("ReqU ( _v_: an ECMAScript language value ): either a normal completion containing ~unused~ or a throw completion", "    1. If _v_ is not *undefined*, throw a *TypeError* exception.\n    1. Return ~unused~."),
    ]) + &builtin_fn("sec-foo.c", "Foo.c ( _x_ )", "    1. Perform ? ReqU(_x_).\n    1. If _x_ is not present, return Str(_x_).\n    1. Return *true*.");
    let (sp, g, dt, td) = ty_data(&html);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    // ReqU returned with *undefined*, which a parameter not passed reads as
    assert_eq!(f, ["disjoint\tsec-foo.c#0\t2\tStr argument 1 (_s_): Undefined for String"]);
}

#[test]
fn a_field_write_through_an_unknown_base_is_checked_at_every_kind() {
    let g = overlay_grammar(
        "spec-gen-field-write-alias",
        r#"<emu-clause id="formal-x">
  <emu-sort name="Foo Record" record clause="sec-0"></emu-sort>
  <emu-sort name="Bar Record" record clause="sec-0"></emu-sort>
</emu-clause>
"#,
    );
    let table = |k: &str, t: &str| format!("<emu-table id=\"table-{k}-record\" caption=\"{k} Record Fields\">\n  <table>\n    <tr><th>Field Name</th><th>Value</th><th>Meaning</th></tr>\n    <tr><td>[[Key]]</td><td>{t}</td><td>m</td></tr>\n  </table>\n</emu-table>\n");
    let html = table("Foo", "a String")
        + &table("Bar", "a String or a Number")
        + &aos(&[
            ("Put ( _r_, _v_: an ECMAScript language value ): ~unused~", "    1. Set _r_.[[Key]] to _v_.\n    1. Set _r_.[[Key]] to *\"k\"*.\n    1. Set _r_.[[Key]] to 1.\n    1. Return ~unused~."),
            ("Anon ( ): ~unused~", "    1. Let _a_ be the Record { [[Key]]: 1 }.\n    1. Set _a_.[[Key]] to *true*.\n    1. Return ~unused~."),
        ]);
    let sp = crate::spec::scan(&html).unwrap();
    let rows = classify(&sp, &g);
    let mut dt = crate::data::build(&html, &sp, &g, &rows);
    let ts = crate::tables::build_with(&html, &sp, &g, &mut dt, true);
    let td = crate::tydecls::TyDecls::build(&dt.decls, &ts);
    let f: Vec<String> = crate::types::within(&sp, &g, &dt, &td).0.iter().map(|f| f.line().trim_end().to_string()).collect();
    // the base may be a Foo or a Bar Record, or a Record of no table
    assert_eq!(
        f,
        [
            "unknown\tsec-0#0\t1\t[[Key]] of: Any for Object | Rec",
            "meets\tsec-0#0\t1\ta value set in [[Key]]: LangValue for each of String | Number, or none",
            "unknown\tsec-0#0\t2\t[[Key]] of: Any for Object | Rec",
            "unknown\tsec-0#0\t3\t[[Key]] of: Any for Object | Rec",
            "meets\tsec-0#0\t3\ta value set in [[Key]]: Int for each of String | Number, or none",
            "meets\tsec-1#0\t2\ta value set in [[Key]]: Bool for each of String | Number, or none",
        ]
    );
}

#[test]
fn unwired_nonterminal_in_words() {
    use crate::ast::{Expr, Hole, Part};
    let parts = |w: &str| vec![Part::Text("from ".into()), Part::Hole(Hole::E(Expr::Var(2))), Part::Text(w.into())];
    let ss = " all characters corresponding to a code point on the right-hand side of the |LineTerminator| production";
    let why = crate::residue::unwired("RightHandSideCharacters", &parts(ss), false, crate::residue::Pos::Stmt);
    assert_eq!(why.as_deref(), Some("a nonterminal in the words"));
}

const TWIN_RULE: &str = r#"<emu-clause id="sec-g">
  <h1>Grammar</h1>
  <emu-grammar type="definition">
    A :
      `x` B `;`

    C :
      `x` B `;`

    B :
      `{` `}`
  </emu-grammar>
</emu-clause>
<emu-clause id="sec-static-semantics-referencedbindings" type="sdo">
  <h1>Static Semantics: ReferencedBindings ( ): a List of Parse Nodes</h1>
  <dl class="header">
  </dl>
  <emu-grammar>B : `{` `}`</emu-grammar>
  <emu-alg>
    1. Return a new empty List.
  </emu-alg>
</emu-clause>
<emu-clause id="sec-e">
  <h1>Static Semantics: Early Errors</h1>
  <emu-grammar>A : `x` B `;`</emu-grammar>
  <ul>
    <li>
      For each |IdentifierName| _n_ in the ReferencedBindings of |B|: It is a Syntax Error if _n_ is *"let"*.
    </li>
  </ul>
</emu-clause>
"#;

#[test]
fn a_rule_reading_with_also_holds_on_its_twin_only_at_its_readings() {
    let li = TWIN_RULE.split("<li>").nth(1).unwrap().split("</li>").next().unwrap();
    let sentence = r#"For each |IdentifierName| _n_ in the ReferencedBindings of |B|: It is a Syntax Error if _n_ is *"let"*."#;
    let overlay = format!(
        r#"<emu-erratum id="erratum-Twin" name="Twin" resolution="test262" stops="">
  <emu-reading clause="sec-e" grammar="A : `x` B `;`" rule="0" hash="{}" also="C : `x` B `;`" also-clause="sec-g">
    <p reading="test262">{sentence}</p>
  </emu-reading>
</emu-erratum>
"#,
        crate::text::sha256(li)
    );
    let dir = std::path::PathBuf::from(std::env::var("TEST_TMPDIR").unwrap_or_else(|_| std::env::temp_dir().to_string_lossy().into())).join("spec-gen-twin-rule");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("readings.emu"), overlay).unwrap();
    let g = Grammar::new(crate::overlay::read(dir.to_str().unwrap()).unwrap()).unwrap();
    let sp = crate::spec::scan(TWIN_RULE).unwrap();
    let rows = classify(&sp, &g);
    let dt = crate::data::build(TWIN_RULE, &sp, &g, &rows);
    assert!(dt.anchor_errors.is_empty(), "{:?}", dt.anchor_errors);
    assert_eq!(dt.early.len(), 2);
    let (own, twin) = (&dt.early[0], &dt.early[1]);
    assert!(own.twin.is_none() && !own.body.is_empty());
    // literally the twin holds nothing; at test262 it holds the rule's sentence
    assert_eq!(twin.twin.as_deref(), Some("C : `x` B `;`"));
    assert_eq!(twin.idx, crate::data::TWIN_IDX + own.idx);
    assert!(twin.body.is_empty() && twin.prods != own.prods);
    let (_, alts) = twin.readings.as_ref().unwrap();
    assert!(matches!(alts.as_slice(), [(crate::ast::Reading::Test262, ss)] if !ss.is_empty()), "{}", alts.len());
}
