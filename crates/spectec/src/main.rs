//! `spectec`: ECMA-262 SpecTec parser, roundtripper, prose renderer, and Lean generator.

use spectec::ast::*;
use spectec::emit_grammar;
use spectec::emit_lean;
use spectec::ids::Ids;
use spectec::parse::load_spec_dir;
use spectec::print::print_file;
use spectec::prose::render_clause;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

fn usage() -> &'static str {
    "usage: spectec [--spec-dir=DIR] (roundtrip | prose [--clause=ID] | emit [--lean-dir=DIR] [--grammar-index=FILE])"
}

fn cmd_roundtrip(spec_dir: &Path) -> Result<(), String> {
    let spec = load_spec_dir(spec_dir)?;
    let mut diffs = Vec::new();
    for f in &spec.files {
        let full = spec_dir.join(&f.rel_path);
        let orig = std::fs::read_to_string(&full).map_err(|e| format!("{}: {e}", full.display()))?;
        let printed = print_file(f);
        if orig != printed {
            let line = orig
                .lines()
                .zip(printed.lines())
                .enumerate()
                .find(|(_, (a, b))| a != b)
                .map_or(0, |(i, _)| i + 1);
            diffs.push(format!("{}: roundtrip mismatch around line {line}", f.rel_path));
        }
    }
    if !diffs.is_empty() {
        return Err(diffs.join("\n"));
    }
    println!("ok  spectec roundtrip: {} files identical byte-for-byte", spec.files.len());
    Ok(())
}

fn cmd_prose(spec_dir: &Path, clause: Option<&str>) -> Result<(), String> {
    let spec = load_spec_dir(spec_dir)?;
    if let Some(c) = clause {
        print!("{}", render_clause(&spec, c)?);
        return Ok(());
    }
    for f in &spec.files {
        for item in &f.items {
            if let TopItem::Def(a) = item {
                print!("{}", render_clause(&spec, &a.id.clause)?);
            }
        }
    }
    Ok(())
}

fn cmd_emit(spec_dir: &Path, lean_dir: &Path, grammar_index: Option<&Path>) -> Result<(), String> {
    let spec = load_spec_dir(spec_dir)?;
    let ids = Ids::from_spec(&spec);
    emit_grammar::emit(&spec, &ids, &lean_dir.join("Ecma/Grammar/Gen"), grammar_index)?;
    emit_lean::emit(&spec, &ids, &lean_dir.join("Ecma/Gen"))?;
    println!("ok  spectec emit: generated Lean modules into {}", lean_dir.display());
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let mut spec_dir = PathBuf::from("spec/spectec");
    let mut lean_dir = PathBuf::from("lean");
    let mut grammar_index: Option<PathBuf> = None;
    let mut clause: Option<String> = None;
    let mut cmd: Option<String> = None;

    let mut i = 1;
    while i < args.len() {
        let a = &args[i];
        if let Some(v) = a.strip_prefix("--spec-dir=") {
            spec_dir = v.into();
        } else if a == "--spec-dir" && i + 1 < args.len() {
            i += 1;
            spec_dir = args[i].clone().into();
        } else if let Some(v) = a.strip_prefix("--lean-dir=") {
            lean_dir = v.into();
        } else if a == "--lean-dir" && i + 1 < args.len() {
            i += 1;
            lean_dir = args[i].clone().into();
        } else if let Some(v) = a.strip_prefix("--grammar-index=") {
            grammar_index = Some(v.into());
        } else if a == "--grammar-index" && i + 1 < args.len() {
            i += 1;
            grammar_index = Some(args[i].clone().into());
        } else if let Some(v) = a.strip_prefix("--clause=") {
            clause = Some(v.into());
        } else if a == "--clause" && i + 1 < args.len() {
            i += 1;
            clause = Some(args[i].clone());
        } else if !a.starts_with('-') && cmd.is_none() {
            cmd = Some(a.clone());
        } else {
            eprintln!("{}", usage());
            return ExitCode::from(2);
        }
        i += 1;
    }

    let res = match cmd.as_deref() {
        Some("roundtrip") => cmd_roundtrip(&spec_dir),
        Some("prose") => cmd_prose(&spec_dir, clause.as_deref()),
        Some("emit") => cmd_emit(&spec_dir, &lean_dir, grammar_index.as_deref()),
        _ => {
            eprintln!("{}", usage());
            return ExitCode::from(2);
        }
    };
    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("spectec error: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use spectec::lexer::{lex, TokKind};
    use spectec::parse::parse_str;

    #[test]
    fn lexer_brackets_and_tildes() {
        let out = lex("names [[[Object.prototype]]] $ListConcat([[matched], x]) ~key+value~ [~UnicodeMode, ~UnicodeSetsMode]").unwrap();
        let kinds: Vec<_> = out.tokens.into_iter().map(|t| t.kind).collect();
        assert_eq!(
            kinds,
            vec![
                TokKind::Ident { name: "names".into(), quoted: false },
                TokKind::LBracket,
                TokKind::Field("Object.prototype".into()),
                TokKind::RBracket,
                TokKind::Prim("ListConcat".into()),
                TokKind::LParen,
                TokKind::LBracket,
                TokKind::LBracket,
                TokKind::Ident { name: "matched".into(), quoted: false },
                TokKind::RBracket,
                TokKind::Comma,
                TokKind::Ident { name: "x".into(), quoted: false },
                TokKind::RBracket,
                TokKind::RParen,
                TokKind::Enum("key+value".into()),
                TokKind::LBracket,
                TokKind::Tilde,
                TokKind::Ident { name: "UnicodeMode".into(), quoted: false },
                TokKind::Comma,
                TokKind::Tilde,
                TokKind::Ident { name: "UnicodeSetsMode".into(), quoted: false },
                TokKind::RBracket,
                TokKind::Eof,
            ]
        );
    }

    #[test]
    fn lexer_bnd_vs_q() {
        let out = lex("?x ? x ? #\"set\"").unwrap();
        assert_eq!(
            out.tokens.iter().map(|t| &t.kind).collect::<Vec<_>>(),
            vec![
                &TokKind::Bnd("x".into()),
                &TokKind::Quest,
                &TokKind::Ident { name: "x".into(), quoted: false },
                &TokKind::Quest,
                &TokKind::Ident { name: "set".into(), quoted: true },
                &TokKind::Eof,
            ]
        );
    }

    #[test]
    fn keywords_strictly_sorted() {
        for w in spectec::lexer::KEYWORDS.windows(2) {
            assert!(w[0] < w[1], "KEYWORDS out of order: {:?} >= {:?}", w[0], w[1]);
        }
    }

    #[test]
    fn roundtrip_expr_precedence_and_types() {
        let sample = "\
-- Header

def @sec-demo \"Demo\" (kind ao params [x : seq<Number> | butnot(String, val(undefined)), y : doc \"any value\"] -> completion<Boolean>) vars [x, y] {
  let a = 2 ^ {1 + 3}
  let b = (2 ^ (1 + 3))
  if x is val {1; 2} and {a == b or y is not val {true}} {
    return ? y
  }
  else -> return ?x
}

";
        let sf = parse_str("test.spectec", sample).unwrap();
        let reprinted = print_file(&sf);
        assert_eq!(reprinted, sample);
    }

    #[test]
    fn roundtrip_grammar_rule_and_prose() {
        let sample = "\
grammar lexical

rule lexical |IdentifierStart| [UnicodeMode] :: {
  | [+UnicodeMode] |SyntaxCharacter|
  | [~UnicodeMode] \"a\" |DecimalDigit|? [lookahead not_in { \"b\" }]
  | \"‌\" #label \"zwj\"
}

";
        let sf = parse_str("g.spectec", sample).unwrap();
        assert_eq!(print_file(&sf), sample);

        let alg_sample = "\
def @sec-test \"Test\" (kind ao params [x : Number] -> Boolean) vars [x] {
  if x == 1 -> return true
  return false
}

";
        let spec = Spec { files: vec![parse_str("c.spectec", alg_sample).unwrap()] };
        let p = render_clause(&spec, "sec-test").unwrap();
        assert!(p.contains("Test(_x_ (Number))"));
        assert!(p.contains("If _x_ = 1, Return *true*."));
    }

    #[test]
    fn roundtrip_and_emit_spec_model() {
        let sample = "\
spec_module ProseDemo
import Ecma.Model

namespace Ecma {
  ---! # Demo prose model
  ---!
  ---! Summary line.

  section {
    var (M : Model)

    syntax NumView (Math : Type) {
      | nan
      --- finite value
      | finite (m : Math)
    }
    deriving [Repr, BEq]

    relation Plus {E : Type} (r : Rel(E)) : Rel(E) {
      rule step {a b : E} : Plus(r, a, b) :- r(a, b);
      rule trans {a b c : E} : Plus(r, a, c) :- Plus(r, a, b), Plus(r, b, c);
    }

    laws DemoLaws {
      --- sec-demo:
      --- \"Quoted sentence.\"
      --- Reading: equality holds.
      law eq_comm : forall {α} (x y : M.Seq(α)), x = y <=> y = x;
    }

    def check (xs : List(Nat)) : Nat := match xs with
      | [] => 0
      | x :: _ => x + 1
    end
  }
}
";
        let sf = parse_str("prose/00-demo.spectec", sample).unwrap();
        let reprinted = print_file(&sf);
        assert_eq!(reprinted, sample);
        let TopItem::SpecModule(m) = &sf.items[0] else {
            panic!("expected SpecModule");
        };
        let lean = spectec::spec_model::emit_lean::emit_spec_module(m);
        assert!(lean.starts_with("module\n\npublic import Ecma.Model\n\n@[expose] public section\n"));
        assert!(lean.contains("inductive NumView (Math : Type) where"));
        assert!(lean.contains("inductive Plus {E : Type} (r : Rel E) : Rel E where"));
        assert!(lean.contains("structure DemoLaws : Prop where"));
        assert!(lean.contains("eq_comm : ∀ {α} (x y : M.Seq α), x = y ↔ y = x"));
        assert!(!lean.contains("\n--"));
    }
}
