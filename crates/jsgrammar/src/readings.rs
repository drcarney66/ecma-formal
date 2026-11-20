//! The readings of grammar rules: an `<emu-rule-reading clause=… rule=…
//! hash=…>` of an overlay file (spec/formal/*.emu) holds the definition that
//! replaces the pinned rule: inside an `<emu-erratum>` under that erratum's
//! reading (`reading="test262"`), outside one always (`reading="definition"`,
//! an interpreting reading with an `id`).

/// A reading of a rule, as the overlay has it.
pub struct Reading {
    /// The index of its `<emu-erratum>` among the files' errata, in order; none outside one.
    pub erratum: Option<usize>,
    /// The `name` of its `<emu-erratum>`, whose kept id (`erratum-ids.txt`) the data names; none outside one.
    pub erratum_name: Option<String>,
    /// The overlay file's name.
    pub file: String,
    pub clause: String,
    pub rule: String,
    /// SHA-256 of the pinned definition's text.
    pub hash: String,
    /// The 1-based line of its `<emu-grammar>` tag.
    pub line: usize,
    /// The text between the tags.
    pub text: String,
}

const OPEN_DEFINITION: &str = "<emu-grammar type=\"definition\" reading=\"definition\">";

/// Whether `r` names a subset of `test262` and `proposed`.
fn erratum_reading_ok(r: &str) -> bool {
    !r.is_empty() && r.split(' ').all(|w| w == "test262" || w == "proposed")
}

fn attr(tag: &str, name: &str) -> Option<String> {
    let key = format!(" {name}=\"");
    let i = tag.find(&key)? + key.len();
    let j = tag[i..].find('"')? + i;
    Some(tag[i..j].to_string())
}

/// The readings of the files (name, text), in their order.
pub fn scan(files: &[(&str, &str)]) -> Result<Vec<Reading>, String> {
    let mut out = Vec::new();
    let mut before = 0;
    for (file, s) in files {
        before += scan_file(file, s, before, &mut out)?;
    }
    Ok(out)
}

/// One file's readings, its errata numbered from `before`; the number of its errata.
fn scan_file(file: &str, s: &str, before: usize, out: &mut Vec<Reading>) -> Result<usize, String> {
    let line = |p: usize| s[..p].bytes().filter(|&b| b == b'\n').count() + 1;
    let mut errata = Vec::new();
    let mut at = 0;
    while let Some(i) = s[at..].find("<emu-erratum ") {
        let start = at + i;
        let end = s[start..].find("</emu-erratum>").map(|e| start + e).ok_or("an unclosed emu-erratum")?;
        errata.push(start..end);
        at = end;
    }
    let mut k = 0;
    while let Some(r) = s[k..].find("<emu-rule-reading ") {
        let r = k + r;
        let tag = &s[r..r + s[r..].find('>').ok_or("an unclosed emu-rule-reading")? + 1];
        let get = |n: &str| attr(tag, n).ok_or_else(|| format!("{file}:{}: an emu-rule-reading without {n}", line(r)));
        let erratum = errata.iter().position(|e| e.contains(&r)).map(|e| before + e);
        let erratum_name = match errata.iter().find(|e| e.contains(&r)) {
            Some(e) => {
                let etag = &s[e.start..e.start + s[e.start..].find('>').ok_or("an unclosed emu-erratum")? + 1];
                Some(attr(etag, "name").ok_or_else(|| format!("{file}:{}: an emu-erratum without its name", line(e.start)))?)
            }
            None => None,
        };
        let end = s[r..].find("</emu-rule-reading>").map(|e| r + e).ok_or("an unclosed emu-rule-reading")?;
        let (g, tag_len, close) = match erratum {
            Some(_) => {
                let g = s[r..end].find("<emu-grammar ").map(|g| r + g).ok_or_else(|| format!("{file}:{}: an emu-rule-reading without <emu-grammar>", line(r)))?;
                let gtag_end = s[g..end].find('>').ok_or("an unclosed emu-grammar")?;
                let gtag = &s[g..=g + gtag_end];
                if attr(gtag, "type").as_deref() != Some("definition") || !attr(gtag, "reading").as_deref().is_some_and(erratum_reading_ok) {
                    return Err(format!("{file}:{}: an erratum emu-rule-reading must have type=\"definition\" reading=\"test262|proposed\"", line(g)));
                }
                let close = s[g..end].find("</emu-grammar>").map(|c| g + c).ok_or("an unclosed emu-grammar")?;
                (g, gtag.len(), close)
            }
            None => {
                get("id")?;
                let g = s[r..end].find(OPEN_DEFINITION).map(|g| r + g).ok_or_else(|| format!("{file}:{}: an emu-rule-reading without its definition {OPEN_DEFINITION}", line(r)))?;
                let close = s[g..end].find("</emu-grammar>").map(|c| g + c).ok_or("an unclosed emu-grammar")?;
                (g, OPEN_DEFINITION.len(), close)
            }
        };
        out.push(Reading {
            erratum,
            erratum_name,
            file: file.to_string(),
            clause: get("clause")?,
            rule: get("rule")?,
            hash: get("hash")?,
            line: line(g),
            text: s[g + tag_len..close].to_string(),
        });
        k = end;
    }
    Ok(errata.len())
}

/// An equation row an erratum says names no production of the grammar (`<emu-orphan-row clause=… grammar=…>`
/// in an `<emu-erratum>`): its key block resolves to no production.
pub struct Orphan {
    pub erratum: String,
    pub clause: String,
    pub grammar: String,
}

/// The orphan rows of the files, in order.
pub fn orphans(files: &[(&str, &str)]) -> Result<Vec<Orphan>, String> {
    let mut out = Vec::new();
    for (file, s) in files {
        let mut at = 0;
        while let Some(i) = s[at..].find("<emu-erratum ") {
            let start = at + i;
            let end = s[start..].find("</emu-erratum>").map(|e| start + e).ok_or("an unclosed emu-erratum")?;
            let etag = &s[start..start + s[start..].find('>').ok_or("an unclosed emu-erratum")? + 1];
            let mut k = start;
            while let Some(o) = s[k..end].find("<emu-orphan-row ") {
                let o = k + o;
                let tag = &s[o..o + s[o..].find('>').ok_or("an unclosed emu-orphan-row")? + 1];
                let get = |n: &str| attr(tag, n).ok_or_else(|| format!("{file}: an emu-orphan-row without {n}"));
                out.push(Orphan { erratum: attr(etag, "name").ok_or_else(|| format!("{file}: an emu-erratum without its name"))?, clause: get("clause")?, grammar: unescape(&get("grammar")?) });
                k = o + tag.len();
            }
            at = end;
        }
    }
    Ok(out)
}

/// An attribute's character references, as the generator's key text has them.
fn unescape(s: &str) -> String {
    s.replace("&lt;", "<").replace("&gt;", ">").replace("&quot;", "\"").replace("&amp;", "&")
}

/// The kept erratum ids (`erratum-ids.txt`: `N<TAB>name`, `#` comments): name to id.
pub fn erratum_ids(text: &str) -> std::collections::HashMap<String, usize> {
    text.lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .filter_map(|l| {
            let mut f = l.split('\t');
            Some((f.nth(1)?.to_string(), l.split('\t').next()?.parse().ok()?))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scan_erratum_and_definition() {
        let s = "<emu-erratum id=\"e0\" name=\"E0\">\n</emu-erratum>\n<emu-erratum id=\"e1\" name=\"E1\">\n<emu-rule-reading clause=\"c\" rule=\"A\" hash=\"h\">\n<emu-grammar type=\"definition\" reading=\"test262\">\nA :: `a`\n</emu-grammar>\n</emu-rule-reading>\n</emu-erratum>\n<emu-rule-reading id=\"r\" clause=\"c\" rule=\"B\" hash=\"k\">\n<emu-grammar type=\"definition\" reading=\"definition\">\nB :: `b`\n</emu-grammar>\n</emu-rule-reading>\n<emu-erratum id=\"e2\" name=\"E2\">\n<emu-rule-reading clause=\"c\" rule=\"C\" hash=\"m\">\n<emu-grammar type=\"definition\" reading=\"test262 proposed\">\nC :: `c`\n</emu-grammar>\n</emu-rule-reading>\n</emu-erratum>\n";
        let rs = scan(&[("a.emu", s)]).unwrap();
        assert_eq!(rs.iter().map(|r| (r.erratum, r.rule.as_str(), r.line)).collect::<Vec<_>>(), [(Some(1), "A", 5), (None, "B", 11), (Some(2), "C", 17)]);
        assert_eq!(rs[1].text, "\nB :: `b`\n");
        assert_eq!(rs.iter().map(|r| r.erratum_name.as_deref()).collect::<Vec<_>>(), [Some("E1"), None, Some("E2")]);
        // a later file's errata are numbered after the earlier files'
        let rs = scan(&[("a.emu", s), ("b.emu", s)]).unwrap();
        assert_eq!(rs.iter().map(|r| (r.erratum, r.file.as_str(), r.line)).collect::<Vec<_>>(), [(Some(1), "a.emu", 5), (None, "a.emu", 11), (Some(2), "a.emu", 17), (Some(4), "b.emu", 5), (None, "b.emu", 11), (Some(5), "b.emu", 17)]);
    }

    #[test]
    fn orphans_and_kept_ids() {
        let s = "<emu-erratum id=\"e\" name=\"Z\">\n<emu-orphan-row clause=\"c\" grammar=\"A :: `0`\"></emu-orphan-row>\n</emu-erratum>\n";
        let os = orphans(&[("a.emu", s)]).unwrap();
        assert_eq!(os.iter().map(|o| (o.erratum.as_str(), o.clause.as_str(), o.grammar.as_str())).collect::<Vec<_>>(), [("Z", "c", "A :: `0`")]);
        let ids = erratum_ids("# header\n0\tA\n1\tB\tretired\n7\tZ\n");
        assert_eq!((ids.get("A"), ids.get("B"), ids.get("Z")), (Some(&0), Some(&1), Some(&7)));
    }

    #[test]
    fn scan_refuses() {
        // outside an erratum: an id, and the definition reading
        let no_id = "<emu-rule-reading clause=\"c\" rule=\"B\" hash=\"k\">\n<emu-grammar type=\"definition\" reading=\"definition\">\nB :: `b`\n</emu-grammar>\n</emu-rule-reading>\n";
        assert!(scan(&[("a.emu", no_id)]).is_err());
        let test262 = "<emu-rule-reading id=\"r\" clause=\"c\" rule=\"B\" hash=\"k\">\n<emu-grammar type=\"definition\" reading=\"test262\">\nB :: `b`\n</emu-grammar>\n</emu-rule-reading>\n";
        assert!(scan(&[("a.emu", test262)]).is_err());
        let def_in_erratum = "<emu-erratum id=\"e0\" name=\"E0\">\n<emu-rule-reading clause=\"c\" rule=\"A\" hash=\"h\">\n<emu-grammar type=\"definition\" reading=\"definition\">\nA :: `a`\n</emu-grammar>\n</emu-rule-reading>\n</emu-erratum>\n";
        assert!(scan(&[("a.emu", def_in_erratum)]).is_err());
    }
}
