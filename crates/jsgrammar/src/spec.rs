//! spec.html, scanned by hand: its definition blocks (`<emu-grammar
//! type="definition">`, not the examples) with their clause, line and the prose
//! that says what each is (a supplemental grammar, an Annex B overlay), Annex
//! A's `<emu-prodref>`s, the goal symbols the text names, and the other
//! `<emu-grammar>` blocks (the productions the text names).

use std::collections::BTreeMap;

/// A definition block, as spec.html has it.
pub struct RawBlock {
    /// The id of the innermost `<emu-clause>` or `<emu-annex>` around it.
    pub clause: String,
    /// The 1-based line of the opening `<emu-grammar>` tag.
    pub line: usize,
    /// The text between the tags.
    pub text: String,
    /// What the prose before it says it is.
    pub prose: Prose,
}

/// What the prose before a block says it is.
#[derive(Clone)]
pub enum Prose {
    Main,
    /// "When processing an instance of the production <context> the
    /// interpretation of |cover| is refined using the following grammar:"
    Supplemental {
        context: String,
        cover: String,
    },
    /// An Annex B section's overlay: its section, whether it extends or
    /// replaces (the phrase that says so), and when it applies (the sentence
    /// that says so, or none).
    Overlay {
        section: &'static str,
        mode: &'static str,
        cond: &'static str,
    },
}

/// The Annex B sections with definition blocks: clause id, the constructor of
/// `Grammar.AnnexB`, the phrase of the section's prose that says how
/// it combines with the main grammar, the mode that phrase means, and the
/// constructor of `Grammar.OverlayCond` that says when it applies.
const OVERLAYS: &[(&str, &str, &str, &str, &str)] = &[
    (
        "sec-html-like-comments",
        "htmlLikeComments",
        "is extended as follows",
        "extend",
        "notModule",
    ),
    (
        "sec-regular-expressions-patterns",
        "regExpPatterns",
        "is modified and extended as follows",
        "replace",
        "always",
    ),
    (
        "sec-functiondeclarations-in-ifstatement-statement-clauses",
        "functionDeclarationsInIfStatement",
        "The following augments the |IfStatement| production",
        "extend",
        "nonStrict",
    ),
    (
        "sec-initializers-in-forin-statement-heads",
        "initializersInForIn",
        "The following augments the |ForInOfStatement| production",
        "extend",
        "nonStrict",
    ),
];

/// The conditions of `Grammar.OverlayCond` other than `always`, by the
/// sentence of an Annex B section's own prose (before or after its block) that
/// states it.
const CONDITIONS: &[(&str, &str)] = &[
    (
        "notModule",
        "except that this extension is not allowed when parsing source text using the goal symbol |Module|",
    ),
    ("nonStrict", "This production only applies when parsing non-strict code."),
];

/// Words that would state a condition on an overlay: a section's prose may
/// have them only within one of CONDITIONS' sentences.
const CONDITION_WORDS: &[&str] = &["only applies", "not allowed", "only when", "strict", "|Script|", "|Module|"];

/// A clause's own text: from `start` (after its opening tag) to the first
/// clause tag after it (a subclause's or its own end).
fn own_text(s: &str, start: usize) -> &str {
    let rest = &s[start..];
    let end = ["<emu-clause", "<emu-annex", "</emu-clause>", "</emu-annex>"]
        .iter()
        .filter_map(|t| rest.find(t))
        .min()
        .unwrap_or(rest.len());
    &rest[..end]
}

/// The condition an overlay section's own text states, checked against the
/// one OVERLAYS assumes: its sentence must be there, and no other sentence may
/// state one.
fn check_condition(clause: &str, text: &str, cond: &str) -> Result<(), String> {
    let mut rest = text.to_string();
    for (c, sentence) in CONDITIONS {
        let found = rest.contains(sentence);
        if found != (*c == cond) {
            return Err(if found {
                format!("Annex B section {clause} now says \"{sentence}\" (a condition `{c}` this generator does not assume)")
            } else {
                format!("Annex B section {clause} no longer says \"{sentence}\" (its condition `{cond}`)")
            });
        }
        rest = rest.replace(sentence, "");
    }
    // The block's own text and the cross-references are not prose.
    for w in CONDITION_WORDS {
        if rest.contains(w) {
            return Err(format!(
                "Annex B section {clause}'s prose says \"{w}\" outside the conditions this generator knows"
            ));
        }
    }
    Ok(())
}

/// An `<emu-prodref name="X" a="label">` (Annex A).
pub struct ProdRef {
    pub name: String,
    pub label: Option<String>,
    pub line: usize,
}

/// A goal symbol instance the text names: `|X[args]|`, at a line.
pub struct GoalRef {
    pub text: String,
    pub line: usize,
    /// How the text names it: `Grammar.GoalSrc`'s constructor.
    pub src: &'static str,
}

pub struct Spec {
    pub blocks: Vec<RawBlock>,
    /// The supplemental grammars given as copies of definitions elsewhere.
    pub refined_copies: Vec<RawBlock>,
    pub prodrefs: Vec<ProdRef>,
    pub goals: Vec<GoalRef>,
    /// "must cover an |N|" targets.
    pub must_cover: Vec<GoalRef>,
    /// The other `<emu-grammar>` blocks (not definitions, not examples): the
    /// productions the text names, as SDO keys, in steps and in prose.
    pub keys: Vec<KeyBlock>,
    /// Each clause's enclosing clause.
    pub parents: BTreeMap<String, String>,
}

/// A non-definition `<emu-grammar>` block.
pub struct KeyBlock {
    /// The id of the innermost `<emu-clause>` or `<emu-annex>` around it.
    pub clause: String,
    /// The 1-based line of the opening `<emu-grammar>` tag.
    pub line: usize,
    /// The text between the tags.
    pub text: String,
}

fn line_of(s: &str, pos: usize) -> usize {
    s[..pos].bytes().filter(|&b| b == b'\n').count() + 1
}

fn attr(tag: &str, name: &str) -> Option<String> {
    let key = format!(" {name}=\"");
    let i = tag.find(&key)? + key.len();
    let j = tag[i..].find('"')? + i;
    Some(tag[i..j].to_string())
}

/// The text of the `|X|` references in `s`.
fn bars(s: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = s;
    while let Some(i) = rest.find('|') {
        let after = &rest[i + 1..];
        let Some(j) = after.find('|') else { break };
        out.push(after[..j].to_string());
        rest = &after[j + 1..];
    }
    out
}

pub fn scan(s: &str) -> Result<Spec, String> {
    let mut blocks = Vec::new();
    let mut keys = Vec::new();
    let mut parents = BTreeMap::new();
    let mut prodrefs = Vec::new();
    let mut refined_copies = Vec::new();
    // The open clauses: (id, is an annex, the position after its opening tag).
    let mut stack: Vec<(String, bool, usize)> = Vec::new();
    // Where the prose before the next block starts: the end of the last
    // block, clause tag or paragraph boundary.
    let mut prose_from = 0usize;
    let mut i = 0usize;
    while let Some(off) = s[i..].find('<') {
        let p = i + off;
        let rest = &s[p..];
        if !rest.starts_with("<emu-") && !rest.starts_with("</emu-") {
            i = p + 1;
            continue;
        }
        let end = rest
            .find('>')
            .map(|e| p + e + 1)
            .ok_or_else(|| format!("spec.html:{}: unclosed tag", line_of(s, p)))?;
        let tag = &s[p..end];
        if tag.starts_with("<emu-clause") || tag.starts_with("<emu-annex") {
            let id = attr(tag, "id").ok_or_else(|| format!("spec.html:{}: a clause without an id", line_of(s, p)))?;
            if let Some((parent, _, _)) = stack.last() {
                parents.insert(id.clone(), parent.clone());
            }
            stack.push((id, tag.starts_with("<emu-annex"), end));
            prose_from = end;
        } else if tag == "</emu-clause>" || tag == "</emu-annex>" {
            stack
                .pop()
                .ok_or_else(|| format!("spec.html:{}: unbalanced {tag}", line_of(s, p)))?;
            prose_from = end;
        } else if tag.starts_with("<emu-prodref") {
            let name =
                attr(tag, "name").ok_or_else(|| format!("spec.html:{}: emu-prodref without a name", line_of(s, p)))?;
            prodrefs.push(ProdRef {
                name,
                label: attr(tag, "a"),
                line: line_of(s, p),
            });
        } else if tag.starts_with("<emu-grammar") {
            let close = s[end..]
                .find("</emu-grammar>")
                .map(|c| end + c)
                .ok_or_else(|| format!("spec.html:{}: unclosed emu-grammar", line_of(s, p)))?;
            let attrs = &tag["<emu-grammar".len()..tag.len() - 1];
            match attrs {
                "" => {
                    let (clause, _, _) = stack
                        .last()
                        .ok_or_else(|| format!("spec.html:{}: a grammar outside a clause", line_of(s, p)))?;
                    keys.push(KeyBlock {
                        clause: clause.clone(),
                        line: line_of(s, p),
                        text: s[end..close].to_string(),
                    });
                    // A supplemental grammar given by a copy of a definition
                    // elsewhere ("… is refined using the following grammar:",
                    // then an inline <emu-grammar>): the generator checks the
                    // copy against the definition.
                    let before = &s[prose_from..p];
                    if let Some(k) = before.rfind(REFINED) {
                        if before[k + REFINED.len()..].trim() == "</p>" {
                            let (clause, _, _) = stack
                                .last()
                                .ok_or_else(|| format!("spec.html:{}: a block outside a clause", line_of(s, p)))?
                                .clone();
                            let prose = classify(&clause, false, before, "")
                                .map_err(|e| format!("spec.html:{}: {e}", line_of(s, p)))?;
                            refined_copies.push(RawBlock {
                                clause,
                                line: line_of(s, p),
                                text: s[end..close].to_string(),
                                prose,
                            });
                            prose_from = close + "</emu-grammar>".len();
                        }
                    }
                }
                " example" | " type=\"definition\" example" => {}
                " type=\"definition\"" => {
                    let (clause, _, _) = stack
                        .last()
                        .ok_or_else(|| format!("spec.html:{}: a block outside a clause", line_of(s, p)))?
                        .clone();
                    let in_annex = stack.iter().any(|(_, annex, _)| *annex);
                    let before = &s[prose_from..p];
                    let prose = classify(&clause, in_annex, before, own_text(s, stack.last().unwrap().2))
                        .map_err(|e| format!("spec.html:{}: {e}", line_of(s, p)))?;
                    blocks.push(RawBlock {
                        clause,
                        line: line_of(s, p),
                        text: s[end..close].to_string(),
                        prose,
                    });
                    prose_from = close + "</emu-grammar>".len();
                }
                _ => {
                    return Err(format!(
                        "spec.html:{}: an emu-grammar form this generator does not know: {tag}",
                        line_of(s, p)
                    ))
                }
            }
            i = close + "</emu-grammar>".len();
            continue;
        }
        i = end;
    }
    if !stack.is_empty() {
        return Err("spec.html: unclosed clauses at the end".into());
    }

    // Goal symbols: the grammars' goal symbols (§5.1.1–§5.1.5), ParseText's
    // goals, CreateDynamicFunction's grammar symbols.
    let mut goals = Vec::new();
    let mut must_cover = Vec::new();
    for (n, l) in s.lines().enumerate() {
        let line = n + 1;
        if let Some(k) = l
            .find("starting from the goal symbol")
            .or_else(|| l.find("starting from two alternative goal symbols"))
        {
            let tail = &l[k..];
            let tail = &tail[..tail.find(", that describe").unwrap_or(tail.len())];
            for b in bars(tail) {
                goals.push(GoalRef { text: b, line, src: "grammar" });
            }
        }
        let mut rest = l;
        while let Some(k) = rest.find("ParseText(_") {
            let t = &rest[k..];
            if let Some(c) = t.find(", |") {
                let u = &t[c + 3..];
                if let Some(e) = u.find("|)") {
                    goals.push(GoalRef {
                        text: u[..e].to_string(),
                        line,
                        src: "parseText",
                    });
                }
            }
            rest = &t[1..];
        }
        if let Some(k) = l.find("Grammar_ be the grammar symbol |") {
            let u = &l[k + "Grammar_ be the grammar symbol |".len()..];
            if let Some(e) = u.find('|') {
                goals.push(GoalRef {
                    text: u[..e].to_string(),
                    line,
                    src: "grammarSymbol",
                });
            }
        }
        let mut rest = l;
        while let Some(k) = rest.find("must have the syntax of a") {
            let t = &rest[k..];
            if let Some(b) = bars(t).into_iter().next() {
                goals.push(GoalRef { text: b, line, src: "syntaxOf" });
            }
            rest = &t[1..];
        }
        let mut rest = l;
        while let Some(k) = rest.find("must cover a") {
            let t = &rest[k..];
            if let Some(b) = bars(t).into_iter().next() {
                must_cover.push(GoalRef { text: b, line, src: "mustCover" });
            }
            rest = &t[1..];
        }
    }
    Ok(Spec {
        blocks,
        refined_copies,
        prodrefs,
        goals,
        must_cover,
        keys,
        parents,
    })
}

/// What the prose before a block says it is. `before` is the text since the
/// last block or clause boundary, `clause_text` the clause's own text (before
/// and after the block, up to its first subclause).
const REFINED: &str = "is refined using the following grammar:";

fn classify(clause: &str, in_annex: bool, before: &str, clause_text: &str) -> Result<Prose, String> {
    if let Some(k) = before.rfind(REFINED) {
        let head = &before[..k];
        let ctx_start = head
            .rfind("<emu-grammar>")
            .ok_or("a supplemental grammar without its production")?
            + "<emu-grammar>".len();
        let ctx_end = head[ctx_start..]
            .find("</emu-grammar>")
            .ok_or("an unclosed production")?
            + ctx_start;
        let after = &head[ctx_end..];
        let cover = bars(after)
            .into_iter()
            .last()
            .ok_or("a supplemental grammar without its cover")?;
        if !after.contains(&format!("the interpretation of |{cover}|")) {
            return Err(format!(
                "a supplemental grammar's prose this generator does not know: {}",
                after.trim()
            ));
        }
        return Ok(Prose::Supplemental {
            context: head[ctx_start..ctx_end].to_string(),
            cover,
        });
    }
    if in_annex {
        let (_, ctor, phrase, mode, cond) = OVERLAYS.iter().find(|o| o.0 == clause).ok_or_else(|| {
            format!("a definition block in Annex B section {clause}, which this generator does not know")
        })?;
        if !clause_text.contains(phrase) {
            return Err(format!("Annex B section {clause} no longer says \"{phrase}\""));
        }
        check_condition(clause, &strip_grammar(clause_text), cond)?;
        return Ok(Prose::Overlay {
            section: ctor,
            mode,
            cond,
        });
    }
    Ok(Prose::Main)
}

/// A clause's text without its `<emu-grammar>` blocks (the prose only).
fn strip_grammar(t: &str) -> String {
    let mut out = String::new();
    let mut rest = t;
    while let Some(i) = rest.find("<emu-grammar") {
        out.push_str(&rest[..i]);
        match rest[i..].find("</emu-grammar>") {
            Some(j) => rest = &rest[i + j + "</emu-grammar>".len()..],
            None => {
                rest = "";
                break;
            }
        }
    }
    out.push_str(rest);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const B33: &str = "<p>The following augments the |IfStatement| production in <emu-xref></emu-xref>:</p>\n<emu-grammar type=\"definition\">\n  IfStatement : `if` `(` Expression `)` FunctionDeclaration\n</emu-grammar>\n<p>This production only applies when parsing non-strict code.</p>";

    #[test]
    fn overlay_conditions() {
        assert!(check_condition("b33", &strip_grammar(B33), "nonStrict").is_ok());
        // A condition the table does not assume, or one no longer stated.
        assert!(check_condition("b33", &strip_grammar(B33), "always").is_err());
        let gone = B33.replace("This production only applies when parsing non-strict code.", "");
        assert!(check_condition("b33", &strip_grammar(&gone), "nonStrict").is_err());
        // A reworded condition is not taken for no condition.
        let reworded = B33.replace("only applies when parsing non-strict code", "only applies to sloppy-mode code");
        assert!(check_condition("b33", &strip_grammar(&reworded), "always").is_err());
        let module = "<p>The syntax is extended as follows except that this extension is not allowed when parsing source text using the goal symbol |Module|:</p>";
        assert!(check_condition("b11", module, "notModule").is_ok());
        assert!(check_condition("b11", module, "always").is_err());
    }

    #[test]
    fn own_text_stops_at_a_subclause() {
        let s = "<emu-annex id=\"x\"><p>a</p><emu-annex id=\"y\"><p>b</p></emu-annex></emu-annex>";
        let start = s.find('>').unwrap() + 1;
        assert_eq!(own_text(s, start), "<p>a</p>");
    }
}
