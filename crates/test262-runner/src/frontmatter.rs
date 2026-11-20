//! The YAML frontmatter of a test262 test (`/*--- … ---*/`, see test262's
//! INTERPRETING.md), read by a small line-based parser that understands the
//! shapes test262 uses: `key: value`, inline lists `key: [a, b]`, block lists
//! (`key:` followed by `- item` lines), the `negative:` map, and block
//! scalars (`|`, `>`), which are skipped.

/// When a negative test is expected to fail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Phase {
    /// While parsing, including early errors (`parse`, or the older `early`).
    Parse,
    /// While resolving module imports (`resolution`).
    Resolution,
    /// While evaluating (`runtime`).
    Runtime,
}

/// `negative:`: the phase and the constructor name of the expected error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Negative {
    pub phase: Phase,
    pub error_type: String,
}

/// The metadata the runner uses.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Frontmatter {
    pub flags: Vec<String>,
    pub features: Vec<String>,
    pub includes: Vec<String>,
    pub negative: Option<Negative>,
}

impl Frontmatter {
    pub fn has_flag(&self, flag: &str) -> bool {
        self.flags.iter().any(|f| f == flag)
    }
}

/// Parse the frontmatter of `source`. A test without one has empty metadata.
pub fn parse(source: &str) -> Result<Frontmatter, String> {
    let Some(start) = source.find("/*---") else {
        return Ok(Frontmatter::default());
    };
    let body = &source[start + 5..];
    let Some(end) = body.find("---*/") else {
        return Err("unterminated frontmatter".into());
    };
    // YAML line breaks: LF, CRLF and a lone CR (some tests use CR only).
    let lines: Vec<&str> = body[..end].split(['\n', '\r']).collect();
    let mut fm = Frontmatter::default();
    let mut negative_phase: Option<Phase> = None;
    let mut negative_type: Option<String> = None;
    let mut has_negative = false;
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i];
        i += 1;
        if line.trim().is_empty() || line.starts_with(char::is_whitespace) {
            continue;
        }
        let Some((key, value)) = line.split_once(':') else {
            continue;
        };
        let key = key.trim();
        let value = value.trim();
        // The indented lines that belong to this key.
        let mut nested: Vec<&str> = Vec::new();
        while i < lines.len() && (lines[i].trim().is_empty() || lines[i].starts_with(char::is_whitespace)) {
            nested.push(lines[i]);
            i += 1;
        }
        match key {
            "flags" | "features" | "includes" => {
                let items = if value.starts_with('[') {
                    inline_list(value)?
                } else if value.is_empty() {
                    block_list(&nested)
                } else {
                    return Err(format!("{key}: expected a list, got {value:?}"));
                };
                match key {
                    "flags" => fm.flags = items,
                    "features" => fm.features = items,
                    _ => fm.includes = items,
                }
            }
            "negative" => {
                has_negative = true;
                for l in &nested {
                    if let Some((k, v)) = l.trim().split_once(':') {
                        let v = v.trim().to_string();
                        match k.trim() {
                            "phase" => {
                                negative_phase = Some(match v.as_str() {
                                    "parse" | "early" => Phase::Parse,
                                    "resolution" => Phase::Resolution,
                                    "runtime" => Phase::Runtime,
                                    _ => return Err(format!("negative: unknown phase {v:?}")),
                                })
                            }
                            "type" => negative_type = Some(v),
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
    }
    if has_negative {
        match (negative_phase, negative_type) {
            (Some(phase), Some(error_type)) => fm.negative = Some(Negative { phase, error_type }),
            _ => return Err("negative: needs a phase and a type".into()),
        }
    }
    Ok(fm)
}

/// `[a, b, c]` (possibly empty).
fn inline_list(value: &str) -> Result<Vec<String>, String> {
    let inner = value
        .strip_prefix('[')
        .and_then(|v| v.split('#').next())
        .map(str::trim_end)
        .and_then(|v| v.strip_suffix(']'))
        .ok_or_else(|| format!("unterminated list {value:?}"))?;
    Ok(inner
        .split(',')
        .map(|s| s.trim().trim_matches(|c| c == '"' || c == '\'').to_string())
        .filter(|s| !s.is_empty())
        .collect())
}

/// Indented `- item` lines.
fn block_list(lines: &[&str]) -> Vec<String> {
    lines
        .iter()
        .filter_map(|l| l.trim().strip_prefix('-'))
        .map(|s| s.trim().trim_matches(|c| c == '"' || c == '\'').to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inline_lists_and_negative() {
        let src = "// c\n/*---\nesid: sec-x\ndescription: >\n  a: b\n  flags: [nope]\nflags: [onlyStrict, raw]\n\
                   features: [let, const]\nnegative:\n  phase: parse\n  type: SyntaxError\n---*/\nx;\n";
        let fm = parse(src).unwrap();
        assert_eq!(fm.flags, vec!["onlyStrict", "raw"]);
        assert_eq!(fm.features, vec!["let", "const"]);
        assert!(fm.includes.is_empty());
        assert_eq!(
            fm.negative,
            Some(Negative {
                phase: Phase::Parse,
                error_type: "SyntaxError".into()
            })
        );
    }

    #[test]
    fn block_lists_and_early_phase() {
        let src = "/*---\nincludes:\n  - compareArray.js\n  - propertyHelper.js\nnegative:\n  type: ReferenceError\n  \
                   phase: early\ninfo: |\n  includes: [x]\n---*/";
        let fm = parse(src).unwrap();
        assert_eq!(fm.includes, vec!["compareArray.js", "propertyHelper.js"]);
        assert_eq!(fm.negative.unwrap().phase, Phase::Parse);
    }

    #[test]
    fn carriage_return_line_breaks() {
        let src = "/*---\rincludes: [nativeFunctionMatcher.js]\rflags: [raw]\r---*/\rx;";
        let fm = parse(src).unwrap();
        assert_eq!(fm.includes, vec!["nativeFunctionMatcher.js"]);
        assert_eq!(fm.flags, vec!["raw"]);
        let crlf = "/*---\r\nincludes:\r\n  - a.js\r\n---*/";
        assert_eq!(parse(crlf).unwrap().includes, vec!["a.js"]);
    }

    #[test]
    fn no_frontmatter() {
        assert_eq!(parse("1;").unwrap(), Frontmatter::default());
        assert!(parse("/*--- flags: [a]").is_err());
    }
}
