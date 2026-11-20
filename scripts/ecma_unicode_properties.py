#!/usr/bin/env python3
"""Generate ECMA-262's Unicode properties (lean/Ecma/Unicode/Gen/Properties.lean).

    python3 scripts/ecma_unicode_properties.py          # rewrite the generated Lean file
    python3 scripts/ecma_unicode_properties.py --check  # exit 1 if it is stale
    python3 scripts/ecma_unicode_properties.py --ucd DIR --spec DIR

The properties `\\p{…}` accepts are the three tables of the pinned ECMA-262
(`table-*-unicode-properties*.html` beside the text's spec.html, `scripts/spec_text.py`, or of `--spec DIR`): Table
65 (non-binary), 66 (binary) and 67 (binary properties of strings). The file has their canonical
names as inductive types (`NonBinaryProperty`, `BinaryProperty`, `StringProperty`), their names and
aliases with the constructors they denote, and the total functions from the binary and string
properties to the Unicode library's data (lean/Unicode, scripts/unicode_properties.py): Any, ASCII
and RGI_Emoji (the union of the other six, UTS #51 ED-27) are derived here. A property the tables
name that the Unicode library has no data for is an error.
"""

import argparse
import html
import re
import sys
from pathlib import Path

import spec_text
from unicode_properties import ROOT, Data, binary_sets, default_ucd, header, ident, sequence_sets, write

SCRIPT = "scripts/ecma_unicode_properties.py"
# Not read from a property file: Any and ASCII are ranges, Assigned is GeneralCategory.lean's.
DERIVED_BINARY = {"Any", "ASCII", "Assigned"}


def spec_table(spec: Path, name: str) -> list[tuple[str, str]]:
    """(name or alias, canonical name) for each row of a spec table. A row of
    Tables 65 and 66 with two cells starts a property (its name and canonical
    name); a row with one cell is an alias of the property above it. Table 67
    has one cell per row, the property's name."""
    text = (spec / name).read_text(encoding="utf-8")
    strings = "properties-of-strings" in name
    out = []
    canonical = None
    for row in re.findall(r"<tr>(.*?)</tr>", text, re.DOTALL):
        cells = [
            html.unescape(re.sub(r"<[^>]+>", "", c)).strip().strip("`")
            for c in re.findall(r"<t[dh][^>]*>(.*?)</t[dh]>", row, re.DOTALL)
        ]
        if not cells or cells[0].startswith("Property name"):
            continue
        if strings:
            out.append((cells[0], cells[0]))
            continue
        if len(cells) == 2:
            canonical = cells[1]
        out.append((cells[0], canonical))
    return out


def generate(data: Data, spec: Path) -> dict[str, str]:
    nonbinary = spec_table(spec, "table-nonbinary-unicode-properties.html")
    binary_aliases = spec_table(spec, "table-binary-unicode-properties.html")
    strings_props = [a for a, _ in spec_table(spec, "table-binary-unicode-properties-of-strings.html")]
    nonbinary_canon = list(dict.fromkeys(c for _, c in nonbinary))
    binary_canon = sorted({c for _, c in binary_aliases})
    parts_of_rgi = [p for p in strings_props if p != "RGI_Emoji"]
    have = binary_sets(data)
    missing = [p for p in binary_canon if p not in DERIVED_BINARY and p not in have]
    missing += [p for p in parts_of_rgi if p not in sequence_sets(data)]
    if missing:
        sys.exit(f"the Unicode library has no data for {missing}")

    out = [
        header(
            "ECMA-262's Unicode properties",
            "The canonical property names of ECMA-262 Tables 65 (non-binary), 66 (binary) "
            "and 67 (binary properties of strings) as inductive types, the property names "
            "and aliases with the constructors they denote, and the total functions from "
            "the binary and string properties to the Unicode library's data: Any is every "
            "code point, ASCII U+0000 to U+007F, and RGI_Emoji the union of the other six "
            "properties of strings (UTS #51 ED-27).",
            [
                "Unicode.Gen.GeneralCategory",
                "Unicode.Gen.BinaryProperties1",
                "Unicode.Gen.BinaryProperties2",
                "Unicode.Gen.BinaryProperties3",
                "Unicode.Gen.EmojiSequences",
            ],
            script=SCRIPT,
            namespace="Ecma.Unicode",
            opens="\nopen _root_.Unicode\n",
        )
    ]

    def inductive(name, doc, ctors):
        return (
            f"/-- {doc} -/\ninductive {name} where\n"
            + "".join(f"  | {ident(c)}\n" for c in ctors)
            + "  deriving DecidableEq, Repr\n"
        )

    def pairs(ty, ps):
        return f"List (String × {ty}) := [\n" + ",\n".join(f'  ("{a}", .{ident(c)})' for a, c in ps) + "]"

    out.append(inductive("NonBinaryProperty", "Table 65: the canonical non-binary property names.", nonbinary_canon))
    out.append(inductive("BinaryProperty", "Table 66: the canonical binary property names.", binary_canon))
    out.append(inductive("StringProperty", "Table 67: the binary properties of strings.", strings_props))
    out.append(
        "/-- Table 65: the non-binary property names and aliases, with their canonical names. -/\n"
        "def nonBinaryPropertyNames : " + pairs("NonBinaryProperty", nonbinary) + "\n"
    )
    out.append(
        "/-- Table 66: the binary property names and aliases, with their canonical names. -/\n"
        "def binaryPropertyNames : " + pairs("BinaryProperty", binary_aliases) + "\n"
    )
    out.append(
        "/-- Table 67: the binary properties of strings. -/\n"
        "def stringPropertyNames : " + pairs("StringProperty", [(p, p) for p in strings_props]) + "\n"
    )
    arms = []
    for p in binary_canon:
        if p == "Any":
            arms.append(f"  | .{ident(p)} => [(0x0, 0x10FFFF)]")
        elif p == "ASCII":
            arms.append(f"  | .{ident(p)} => [(0x0, 0x7F)]")
        else:
            arms.append(f"  | .{ident(p)} => Binary.{ident(p)}")
    out.append(
        "/-- The code points whose binary property _p_ is True. -/\n"
        "def BinaryProperty.codePoints : BinaryProperty → List (Nat × Nat)\n" + "\n".join(arms) + "\n"
    )
    arms = [f"  | .{ident(p)} => (Strings.{ident(p)}.ranges, Strings.{ident(p)}.strings)" for p in parts_of_rgi]
    arms.append(
        "  | .«RGI_Emoji» =>\n    ("
        + " ++ ".join(f"Strings.{ident(p)}.ranges" for p in parts_of_rgi)
        + ",\n     "
        + " ++ ".join(f"Strings.{ident(p)}.strings" for p in parts_of_rgi)
        + ")"
    )
    out.append(
        "/-- The sequences of the binary property of strings _p_: the code points that are "
        "sequences of one, as ranges, and the sequences of two or more code points; "
        "RGI_Emoji is the union of the other six (UTS #51 ED-27). -/\n"
        "def StringProperty.elements : StringProperty → List (Nat × Nat) × List (List Nat)\n" + "\n".join(arms) + "\n"
    )
    out.append("end Ecma.Unicode\n")
    return {"Ecma/Unicode/Gen/Properties.lean": "\n".join(out)}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="exit 1 if the generated file is stale")
    ap.add_argument("--ucd", type=Path, help="the UCD's files (default: $UNICODE_UCD)")
    ap.add_argument("--spec", type=Path, help="the ECMA-262 source (default: the text's directory, scripts/spec_text.py)")
    args = ap.parse_args()
    args.spec = args.spec or spec_text.spec_dir()
    if not (args.spec / "table-binary-unicode-properties.html").exists():
        sys.exit(f"{args.spec} has no ECMA-262 source: run `git submodule update --init external/ecma262`, or pass --spec DIR")
    return write(generate(Data(args.ucd or default_ucd()), args.spec), args.check, SCRIPT)


if __name__ == "__main__":
    sys.exit(main())
