//! The kept id tables (`spec/formal/clause-ids.txt`, `sdo-ids.txt`, `method-ids.txt`, `erratum-ids.txt`, `reason-ids.txt`,
//! `note-ids.txt`, `table-ids.txt`; the grammar's are crates/jsgrammar's `ids`): a number
//! per name, so that a change to the specification's text renumbers nothing it does not change.
//!
//! A table is `#` comment lines, then a line `N<TAB>name` per id in id order; a name the text no longer has keeps
//! its number, marked `<TAB>retired`; a name a clause's `oldids` renamed records the old names, `<TAB>was old …`.
//! The generator reads the table, gives each name met its number and each new name the next unused number (in the
//! order it meets them), and writes the table back (`scripts/gen_spec.py --write`).

use crate::ast::Id;
use crate::decls::Table;
use std::collections::BTreeMap;

#[derive(Clone, Debug, Default)]
pub struct Entry {
    pub id: Id,
    pub name: String,
    /// the names it had before (`oldids`)
    pub was: Vec<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Kept {
    pub entries: Vec<Entry>,
}

impl Kept {
    /// The names it records as renamed, by id.
    pub fn was(&self) -> BTreeMap<Id, Vec<String>> {
        self.entries.iter().filter(|e| !e.was.is_empty()).map(|e| (e.id, e.was.clone())).collect()
    }
}

/// A kept table's file names in the overlay directory, and their headers.
pub const CLAUSE_IDS: &str = "clause-ids.txt";
pub const SDO_IDS: &str = "sdo-ids.txt";
pub const METHOD_IDS: &str = "method-ids.txt";
pub const ERRATUM_IDS: &str = "erratum-ids.txt";
pub const REASON_IDS: &str = "reason-ids.txt";
pub const NOTE_IDS: &str = "note-ids.txt";
pub const TABLE_IDS: &str = "table-ids.txt";

pub fn header(file: &str) -> &'static str {
    match file {
        CLAUSE_IDS => "# The clause ids (`ClauseId`, the first component of an `AlgId`; `Ecma.Gen.clauses`): spec.html's clauses
# by their id attribute (a parameterized clause's instances as `sec-x/Name`), then the overlay's algorithms
# (phrases' and sorts' steps, row readings, the sorts' context phrases) by their overlay id.
# The generator gives a clause met its number here and a new one the next unused number, and writes this file
# (scripts/gen_spec.py --write); a clause the text no longer has keeps its number, marked retired, and a clause
# whose `oldids` names an entry takes that entry's number (`was`). Do not renumber or reuse a line by hand.",
        SDO_IDS => "# The syntax-directed operation ids (`SdoId`; `Ecma.Gen.sdos`), by the operation's name.
# The generator gives an operation met its number here and a new one the next unused number, and writes this
# file (scripts/gen_spec.py --write); one the text no longer has keeps its number, marked retired.
# Do not renumber or reuse a line by hand.",
        METHOD_IDS => "# The concrete-method name ids (`MethodId`; `Ecma.Gen.methods`), by the method's name.
# The generator gives a name met its number here and a new one the next unused number, and writes this file
# (scripts/gen_spec.py --write); one the text no longer has keeps its number, marked retired.
# Do not renumber or reuse a line by hand.",
        ERRATUM_IDS => "# The erratum ids (`ErratumId`; `Ecma.Gen.errata`, `errataIds`, `parity`): the overlay's errata by their name,
# then its definition readings (`<emu-reading steps=…>` outside an erratum) by theirs (`definition-CLAUSE-STEP`).
# The first ones are those `Ecma.Known` reads (crates/spec-gen data.rs KNOWN_ERRATA). The generator gives an
# erratum met its number here and a new one the next unused number, and writes this file (scripts/gen_spec.py
# --write); one the overlay no longer has keeps its number, marked retired. Do not renumber or reuse a line by hand.",
        REASON_IDS => "# The residue channel (a) reason ids (`.upstream N`; `Ecma.Gen.reasons`), by the reason's text.
# The generator gives a reason met its number here and a new one the next unused number, and writes this file
# (scripts/gen_spec.py --write); one no longer given keeps its number, marked retired. Do not renumber by hand.",
        NOTE_IDS => "# The residue channel (c) kind ids (`.annotated N`; `Ecma.Gen.notes`), by the kind's text.
# The generator gives a kind met its number here and a new one the next unused number, and writes this file
# (scripts/gen_spec.py --write); one no longer given keeps its number, marked retired. Do not renumber by hand.",
        TABLE_IDS => "# The table ids (`TableId`; `.table N`, `.tableStep N`; `Ecma.Gen.tables` flattened), by the table's Lean name:
# its id attribute, else its clause's id and its index there (`sec-x-table-N`). The generator gives a table met
# its number here and a new one the next unused number, and writes this file (scripts/gen_spec.py --write); one
# the text no longer has keeps its number, its entry `Table.retired`, marked retired. Do not renumber by hand.",
        _ => "",
    }
}

/// The table in `dir/file`, if there is one.
pub fn read(dir: &str, file: &str) -> Result<Option<Kept>, String> {
    let path = format!("{dir}/{file}");
    let Ok(s) = std::fs::read_to_string(&path) else { return Ok(None) };
    let mut k = Kept::default();
    let mut names = std::collections::HashSet::new();
    for (n, l) in s.lines().enumerate() {
        if l.starts_with('#') || l.is_empty() {
            continue;
        }
        let bad = |why: &str| format!("{path}:{}: {why}: {l}", n + 1);
        let mut f = l.split('\t');
        let id: Id = f.next().and_then(|x| x.parse().ok()).ok_or_else(|| bad("not `N<TAB>name`"))?;
        let name = f.next().filter(|x| !x.is_empty()).ok_or_else(|| bad("no name"))?.to_string();
        let mut was = Vec::new();
        for x in f {
            if let Some(w) = x.strip_prefix("was ") {
                was.extend(w.split(' ').map(str::to_string));
            } else if x != "retired" {
                return Err(bad("a third field neither `retired` nor `was …`"));
            }
        }
        if k.entries.last().is_some_and(|e| e.id >= id) {
            return Err(bad("not in increasing id order"));
        }
        if !names.insert(name.clone()) {
            return Err(bad("a second line for the name"));
        }
        k.entries.push(Entry { id, name, was });
    }
    Ok(Some(k))
}

/// The table's text for `t`: every id with a name, retired where this run did not intern it, with the
/// renames `was` records.
pub fn render(file: &str, t: &Table, was: &BTreeMap<Id, Vec<String>>) -> String {
    let mut o = String::new();
    o.push_str(header(file));
    o.push('\n');
    for (i, n) in t.names.iter().enumerate().filter(|(_, n)| !n.is_empty()) {
        o.push_str(&format!("{i}\t{n}"));
        if t.retired(i) {
            o.push_str("\tretired");
        }
        if let Some(w) = was.get(&i).filter(|w| !w.is_empty()) {
            o.push_str(&format!("\twas {}", w.join(" ")));
        }
        o.push('\n');
    }
    o
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table(text: &str) -> Kept {
        let dir = std::env::temp_dir().join(format!("spec-gen-ids-{}-{}", std::process::id(), text.len()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join(CLAUSE_IDS), text).unwrap();
        let k = read(dir.to_str().unwrap(), CLAUSE_IDS).unwrap().unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        k
    }

    #[test]
    fn kept_numbers_new_names_retired_and_renamed() {
        let k = table("# h\n0\tsec-a\n1\tsec-b\n2\tsec-c\tretired\n3\tsec-d\twas sec-old\n");
        let mut d = crate::decls::Decls::default();
        d.clauses.seed(&k);
        d.clause_was = k.was();
        // sec-c comes back, sec-a is gone, sec-e is new, sec-f was sec-b
        assert_eq!(d.intern_clause("sec-c", &[]), 2);
        assert_eq!(d.intern_clause("sec-d", &[]), 3);
        assert_eq!(d.intern_clause("sec-e", &[]), 4);
        assert_eq!(d.intern_clause("sec-f", &["sec-x".into(), "sec-b".into()]), 1);
        // an old id already renamed or met is not taken twice
        assert_eq!(d.intern_clause("sec-g", &["sec-b".into(), "sec-c".into()]), 5);
        let out = render(CLAUSE_IDS, &d.clauses, &d.clause_was);
        let body: Vec<&str> = out.lines().filter(|l| !l.starts_with('#')).collect();
        assert_eq!(body, ["0\tsec-a\tretired", "1\tsec-f\twas sec-b", "2\tsec-c", "3\tsec-d\twas sec-old", "4\tsec-e", "5\tsec-g"]);
        assert_eq!(d.ops.len(), 6);
    }

    #[test]
    fn a_table_reads_back_as_written() {
        let text = format!("{}\n0\tx\n2\ty\tretired\n5\tz\twas a b\n", header(SDO_IDS));
        let k = table(&text);
        let mut t = Table::default();
        t.seed(&k);
        t.intern("x");
        t.intern("z");
        assert_eq!(render(SDO_IDS, &t, &k.was()), text);
        assert!(t.retired(2) && !t.retired(0) && !t.retired(1));
    }

    #[test]
    fn a_table_out_of_order_or_with_a_name_twice_is_refused() {
        for bad in ["1\tx\n0\ty\n", "0\tx\n1\tx\n", "0\n", "x\ty\n", "0\tx\tgone\n"] {
            let dir = std::env::temp_dir().join(format!("spec-gen-ids-bad-{}-{}", std::process::id(), bad.len()));
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(dir.join(NOTE_IDS), bad).unwrap();
            assert!(read(dir.to_str().unwrap(), NOTE_IDS).is_err(), "{bad:?}");
            std::fs::remove_dir_all(&dir).unwrap();
        }
    }
}
