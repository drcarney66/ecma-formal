//! ECMA-262's grammars (GL) from the pinned spec.html: the definition blocks
//! parsed (`grammar`, `spec`), one numbering of their nonterminals and
//! right-hand sides (`gl`, by the kept tables of `ids`), and the resolver of the spec's other
//! `<emu-grammar>` blocks to those ids (`keys`). The binary writes GL as Lean
//! data (docs/parser/GRAMMAR.md).

pub mod gl;
pub mod grammar;
pub mod ids;
pub mod keys;
pub mod spec;
