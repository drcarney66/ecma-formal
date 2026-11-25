//! Retained ID table loading and lookup (`spec/ids/*-ids.txt` or `build/ids/*-ids.txt`).
//!
//! Two table formats exist on disk:
//! 1. Numbered tab-delimited (`clause`, `method`, `nt`, `param`, `prod`, `sdo`, `table`):
//!    `<id>\t<name>[\tretired]`
//! 2. Unnumbered 1-per-line (`enum`, `field`, `prim`, `sort`): `<name>` (0-based row index)

use std::collections::BTreeMap;
use std::path::Path;

#[derive(Clone, Debug)]
pub struct IdTable {
    pub file_name: &'static str,
    pub numbered: bool,
    pub header: Vec<String>,
    pub names: Vec<String>,
    pub retired: Vec<bool>,
    pub notes: Vec<Option<String>>,
    pub by_name: BTreeMap<String, usize>,
}

impl IdTable {
    pub fn load(dir: &Path, file_name: &'static str, numbered: bool) -> Result<Self, String> {
        let path = dir.join(file_name);
        let text = std::fs::read_to_string(&path)
            .map_err(|e| format!("reading {}: {e}", path.display()))?;
        Self::parse(&text, file_name, numbered)
            .map_err(|e| format!("parsing {}: {e}", path.display()))
    }

    pub fn parse(text: &str, file_name: &'static str, numbered: bool) -> Result<Self, String> {
        let mut header = Vec::new();
        let mut names = Vec::new();
        let mut retired = Vec::new();
        let mut notes = Vec::new();
        let mut by_name = BTreeMap::new();
        let mut in_header = true;
        for (line_no, raw) in text.lines().enumerate() {
            let line = raw.trim_end_matches('\r');
            if in_header && (line.is_empty() || line.starts_with('#')) {
                header.push(line.to_string());
                continue;
            }
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            in_header = false;
            if numbered {
                let mut cols = line.split('\t');
                let id_str = cols.next().ok_or_else(|| format!("line {}: empty", line_no + 1))?;
                let id: usize = id_str
                    .parse()
                    .map_err(|_| format!("line {}: bad id `{id_str}`", line_no + 1))?;
                if id != names.len() {
                    return Err(format!(
                        "line {}: expected contiguous id {}, got {id}",
                        line_no + 1,
                        names.len()
                    ));
                }
                let name = cols
                    .next()
                    .ok_or_else(|| format!("line {}: missing name column", line_no + 1))?
                    .to_string();
                let note = cols.next().map(|s| s.to_string());
                let is_ret = note.as_deref() == Some("retired");
                if cols.next().is_some() {
                    return Err(format!("line {}: extra tab column", line_no + 1));
                }
                if by_name.insert(name.clone(), id).is_some() {
                    return Err(format!("line {}: duplicate name `{name}`", line_no + 1));
                }
                names.push(name);
                retired.push(is_ret);
                notes.push(note);
            } else {
                if line.contains('\t') {
                    return Err(format!("line {}: unexpected tab in unnumbered table", line_no + 1));
                }
                let id = names.len();
                let name = line.to_string();
                if by_name.insert(name.clone(), id).is_some() {
                    return Err(format!("line {}: duplicate name `{name}`", line_no + 1));
                }
                names.push(name);
                retired.push(false);
                notes.push(None);
            }
        }
        Ok(Self {
            file_name,
            numbered,
            header,
            names,
            retired,
            notes,
            by_name,
        })
    }

    pub fn get(&self, name: &str) -> Result<usize, String> {
        self.by_name
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown entry `{name}` in {}", self.file_name))
    }

    pub fn get_or_intern(&mut self, name: &str) -> usize {
        if let Some(&id) = self.by_name.get(name) {
            return id;
        }
        let id = self.names.len();
        self.names.push(name.to_string());
        self.retired.push(false);
        self.notes.push(None);
        self.by_name.insert(name.to_string(), id);
        id
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        for h in &self.header {
            out.push_str(h);
            out.push('\n');
        }
        for (id, (name, note)) in self.names.iter().zip(&self.notes).enumerate() {
            if self.numbered {
                if let Some(n) = note {
                    out.push_str(&format!("{id}\t{name}\t{n}\n"));
                } else {
                    out.push_str(&format!("{id}\t{name}\n"));
                }
            } else {
                out.push_str(name);
                out.push('\n');
            }
        }
        out
    }
}

#[derive(Clone, Debug)]
pub struct Ids {
    pub clause: IdTable,
    pub enum_: IdTable,
    pub field: IdTable,
    pub method: IdTable,
    pub nt: IdTable,
    pub param: IdTable,
    pub prim: IdTable,
    pub prod: IdTable,
    pub sdo: IdTable,
    pub sort: IdTable,
    pub table: IdTable,
}

impl Ids {
    pub fn load(dir: &Path) -> Result<Self, String> {
        Ok(Self {
            clause: IdTable::load(dir, "clause-ids.txt", true)?,
            enum_: IdTable::load(dir, "enum-ids.txt", false)?,
            field: IdTable::load(dir, "field-ids.txt", false)?,
            method: IdTable::load(dir, "method-ids.txt", true)?,
            nt: IdTable::load(dir, "nt-ids.txt", true)?,
            param: IdTable::load(dir, "param-ids.txt", true)?,
            prim: IdTable::load(dir, "prim-ids.txt", false)?,
            prod: IdTable::load(dir, "prod-ids.txt", true)?,
            sdo: IdTable::load(dir, "sdo-ids.txt", true)?,
            sort: IdTable::load(dir, "sort-ids.txt", false)?,
            table: IdTable::load(dir, "table-ids.txt", true)?,
        })
    }

    pub fn save_if_changed(&self, dir: &Path) -> Result<(), String> {
        std::fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        let all = [
            &self.clause, &self.enum_, &self.field, &self.method, &self.nt,
            &self.param, &self.prim, &self.prod, &self.sdo, &self.sort, &self.table,
        ];
        for tbl in all {
            let p = dir.join(tbl.file_name);
            let txt = tbl.render();
            if std::fs::read_to_string(&p).ok().as_deref() != Some(&txt) {
                std::fs::write(&p, txt).map_err(|e| format!("{}: {e}", p.display()))?;
            }
        }
        Ok(())
    }
}
