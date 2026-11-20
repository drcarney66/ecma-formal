#!/usr/bin/env python3
"""Generate the Unicode property tables of the Unicode library (lean/Unicode).

    python3 scripts/unicode_properties.py          # rewrite the generated Lean files (below)
    python3 scripts/unicode_properties.py --check  # exit 1 if one is stale
    python3 scripts/unicode_properties.py --ucd DIR

Everything here is the Unicode Character Database's alone (flake.nix's `ucd`; the dev shell names
its directory UNICODE_UCD, which `--ucd DIR` overrides), checked against the SHA-256 sums below.
ECMA-262's own choice of properties is scripts/ecma_unicode_properties.py's (lean/Ecma/Unicode),
which shares this script's reader.

Generated files (lean/Unicode/Gen/):

* GeneralCategory.lean: the code points of each General_Category value that is not a group
  (extracted/DerivedGeneralCategory.txt; Cn is every code point not listed), and Assigned, the
  complement of Unassigned;
* Scripts.lean: the code points of each Script value (Scripts.txt; Unknown is every code point
  not listed) and of each Script_Extensions value: a code point listed in ScriptExtensions.txt has
  the scripts listed there, any other code point its Script;
* BinaryProperties1.lean … 3: the code points of every binary property of PropList.txt,
  DerivedCoreProperties.txt, extracted/DerivedBinaryProperties.txt, DerivedNormalizationProps.txt
  and emoji/emoji-data.txt;
* EmojiSequences.lean: every sequence type of emoji-sequences.txt and emoji-zwj-sequences.txt;
* Classes.lean: ID_Start, ID_Continue and Space_Separator with their membership tests;
* PropertyValues.lean: the canonical (long) values of General_Category and Script as inductive
  types (`GeneralCategoryValue`, `ScriptValue`), their value aliases, and the total functions from
  them to their code points (a General_Category value that groups others, such as `L`, is the
  union of the values it groups);
* PropertyValueAliases.lean: every property's names (PropertyAliases.txt) and value names
  (PropertyValueAliases.txt), as Strings.

Each set is a list of sorted, disjoint, non-adjacent inclusive ranges `(first, last)`; a sequence
type also has the List of its sequences of two or more code points.
"""

import argparse
import hashlib
import io
import os
import sys
import textwrap
import zipfile
from collections import defaultdict
from pathlib import Path

ROOT = Path(os.path.abspath(__file__)).parent.parent
VERSION = "17.0.0"

# The files of the UCD (flake.nix's `ucd`) and their SHA-256 sums.
FILES = {
    "UCD.zip": "2066d1909b2ea93916ce092da1c0ee4808ea3ef8407c94b4f14f5b7eb263d28e",
    "emoji-sequences.txt": "12cc8267dc33cbd11ed32bcf6fc5dc2ad9c7a77bae1bdfba2f41b1b9b3ead8dd",
    "emoji-zwj-sequences.txt": "5b25441daed2322b068c5e70cda522946a4f0274df864445a1965a92e5fc5cad",
}

BINARY_SOURCES = [
    "PropList.txt",
    "DerivedCoreProperties.txt",
    "extracted/DerivedBinaryProperties.txt",
    "DerivedNormalizationProps.txt",
    "emoji/emoji-data.txt",
]

MAX = 0x10FFFF


def default_ucd() -> Path:
    """The dev shell's UCD directory (UNICODE_UCD)."""
    ucd = os.environ.get("UNICODE_UCD")
    if not ucd:
        sys.exit("UNICODE_UCD is unset: run in the dev shell, or pass --ucd DIR")
    return Path(ucd)


class Data:
    """The UCD files, from their directory."""

    def __init__(self, ucd: Path):
        self.dir = ucd
        for name, sha in FILES.items():
            path = ucd / name
            if not path.exists():
                sys.exit(f"{path} is missing (--ucd: flake.nix's `ucd`, the dev shell's UNICODE_UCD)")
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            if digest != sha:
                sys.exit(f"{path}: SHA-256 {digest}, expected {sha}")
        self.zip = zipfile.ZipFile(ucd / "UCD.zip")

    def lines(self, name: str):
        if name.startswith("emoji-") and (self.dir / name).exists():
            text = (self.dir / name).read_text(encoding="utf-8")
        else:
            text = self.zip.read(name).decode("utf-8")
        for line in io.StringIO(text):
            line = line.split("#", 1)[0].strip()
            if line:
                yield [f.strip() for f in line.split(";")]


def code_points(field: str) -> range:
    if ".." in field:
        a, b = field.split("..")
        return range(int(a, 16), int(b, 16) + 1)
    return range(int(field, 16), int(field, 16) + 1)


def ranges_of(cps) -> list[tuple[int, int]]:
    """Sorted, disjoint, non-adjacent inclusive ranges of a set of code points."""
    out: list[list[int]] = []
    for c in sorted(set(cps)):
        if out and out[-1][1] + 1 == c:
            out[-1][1] = c
        else:
            out.append([c, c])
    return [(a, b) for a, b in out]


def value_aliases(data: Data, prop: str):
    """(aliases, long name) of each value of `prop` in PropertyValueAliases.txt,
    and the groups (`# Cc | Cf …` comments) of General_Category."""
    values = []
    text = data.zip.read("PropertyValueAliases.txt").decode("utf-8")
    groups = {}
    for raw in io.StringIO(text):
        body, _, comment = raw.partition("#")
        fields = [f.strip() for f in body.split(";")]
        if len(fields) < 3 or fields[0] != prop:
            continue
        short, long_ = fields[1], fields[2]
        aliases = [short, long_] + [f for f in fields[3:] if f]
        values.append((aliases, long_))
        if prop == "gc" and "|" in comment:
            groups[long_] = [p.strip() for p in comment.split("|")]
    return values, groups


def lean_ranges(rs) -> str:
    items = [f"(0x{a:X}, 0x{b:X})" for a, b in rs]
    lines = []
    for i in range(0, len(items), 6):
        lines.append("    " + ", ".join(items[i : i + 6]))
    return "[\n" + ",\n".join(lines) + "]" if items else "[]"


def lean_sequences(seqs) -> str:
    items = ["[" + ", ".join(f"0x{c:X}" for c in s) + "]" for s in seqs]
    lines = []
    for i in range(0, len(items), 4):
        lines.append("    " + ", ".join(items[i : i + 4]))
    return "[\n" + ",\n".join(lines) + "]" if items else "[]"


def ident(name: str) -> str:
    return f"«{name}»"


HEADER = """module

{imports}
@[expose] public section

/-!
# {title}

Generated by `{script}` from the Unicode Character
Database {version} (do not edit). {doc}
-/

namespace {namespace}
{opens}"""


def header(title: str, doc: str, imports: list[str], script: str = "scripts/unicode_properties.py",
           namespace: str = "Unicode", opens: str = "") -> str:
    imp = "".join(f"public import {m}\n" for m in imports)
    text = HEADER.format(imports=imp, title=title, version=VERSION, doc=doc, script=script, namespace=namespace, opens=opens).replace("module\n\n\n", "module\n\n", 1)
    start = text.index("Generated by")
    end = text.index("\n-/", start)
    body = textwrap.fill(" ".join(text[start:end].split()), width=78)
    return text[:start] + body + text[end:]


CLASSES = """module

@[expose] public section

/-!
# Code point classes: ID_Start, ID_Continue, Space_Separator

Generated by `scripts/unicode_properties.py` from the Unicode Character
Database {version} (do not edit).

ID_Start and ID_Continue (DerivedCoreProperties.txt) and General_Category
Space_Separator as sorted
inclusive ranges, and their membership tests (a binary search over arrays
built on first use).
-/

namespace Unicode

def idStartRanges : List (Nat × Nat) := {id_start}

def idContinueRanges : List (Nat × Nat) := {id_continue}

def spaceSeparatorRanges : List (Nat × Nat) := {space_separator}

def idStartTable : Thunk (Array (Nat × Nat)) := Thunk.mk fun _ => idStartRanges.toArray
def idContinueTable : Thunk (Array (Nat × Nat)) := Thunk.mk fun _ => idContinueRanges.toArray

/-- Whether code point `c` is in the sorted ranges `t`. -/
def inClassRanges (t : Array (Nat × Nat)) (c : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := t.size
  for _ in [0:64] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (a, b) := t[mid]!
    if c < a then hi := mid
    else if b < c then lo := mid + 1
    else return true
  return false

/-- ID_Start. -/
def idStart (c : Nat) : Bool := inClassRanges idStartTable.get c

/-- ID_Continue. -/
def idContinue (c : Nat) : Bool := inClassRanges idContinueTable.get c

/-- General_Category Space_Separator. -/
def spaceSeparator (c : Nat) : Bool := spaceSeparatorRanges.any fun (a, b) => a ≤ c && c ≤ b

end Unicode
"""


def binary_sets(data: Data) -> dict[str, set[int]]:
    """The code points of every binary property the UCD's property files list (a line of two fields:
    code points and the property's name)."""
    sets: dict[str, set[int]] = defaultdict(set)
    for src in BINARY_SOURCES:
        for f in data.lines(src):
            if len(f) == 2:
                sets[f[1]].update(code_points(f[0]))
    return dict(sets)


def sequence_sets(data: Data) -> dict[str, list[list[int]]]:
    """The sequences of every type of the emoji sequence files, in the files' order of types."""
    seqs: dict[str, list[list[int]]] = defaultdict(list)
    for name in ("emoji-sequences.txt", "emoji-zwj-sequences.txt"):
        for f in data.lines(name):
            if " " in f[0]:
                seqs[f[1]].append([int(c, 16) for c in f[0].split()])
            else:
                seqs[f[1]].extend([[c] for c in code_points(f[0])])
    return dict(seqs)


def generate(data: Data) -> dict[str, str]:
    files = {}

    # General_Category
    gc_values, gc_groups = value_aliases(data, "gc")
    short_to_long = {aliases[0]: long_ for aliases, long_ in gc_values}
    listed: dict[str, set[int]] = defaultdict(set)
    for f in data.lines("extracted/DerivedGeneralCategory.txt"):
        listed[short_to_long[f[1]]].update(code_points(f[0]))
    # The file lists the Cn ranges too; a code point it does not list is also
    # Unassigned. Assigned is every code point whose General_Category is not
    # Unassigned (UTS #18 RL1.2), so it is computed after Unassigned is complete.
    listed["Unassigned"] |= set(range(MAX + 1)) - set().union(*listed.values())
    assigned = set(range(MAX + 1)) - listed["Unassigned"]
    basic = [long_ for _, long_ in gc_values if long_ not in gc_groups]
    out = [
        header(
            "Unicode data: General_Category",
            "The code points of each General_Category value that does not group others "
            "(extracted/DerivedGeneralCategory.txt; Unassigned (Cn) is also every code "
            "point that file does not list), and the binary property Assigned, every "
            "other code point.",
            [],
        )
    ]
    for v in basic:
        out.append(
            f"/-- General_Category={v}. -/\ndef GeneralCategory.{ident(v)} : List (Nat × Nat) := "
            + lean_ranges(ranges_of(listed[v]))
            + "\n"
        )
    out.append(
        "/-- The binary property Assigned (UTS #18 RL1.2): every code point whose General_Category "
        "is not Unassigned. -/\ndef Binary.«Assigned» : List (Nat × Nat) := " + lean_ranges(ranges_of(assigned)) + "\n"
    )
    out.append("end Unicode\n")
    files["Unicode/Gen/GeneralCategory.lean"] = "\n".join(out)

    # Script and Script_Extensions
    sc_values, _ = value_aliases(data, "sc")
    sc_short_to_long = {aliases[0]: long_ for aliases, long_ in sc_values}
    sc_sets: dict[str, set[int]] = defaultdict(set)
    script_of: dict[int, str] = {}
    for f in data.lines("Scripts.txt"):
        for c in code_points(f[0]):
            sc_sets[f[1]].add(c)
            script_of[c] = f[1]
    unknown = set(range(MAX + 1)) - set(script_of)
    sc_sets["Unknown"] |= unknown
    for c in unknown:
        script_of[c] = "Unknown"
    scx_sets: dict[str, set[int]] = {k: set(v) for k, v in sc_sets.items()}
    for f in data.lines("ScriptExtensions.txt"):
        scripts = [sc_short_to_long[s] for s in f[1].split()]
        for c in code_points(f[0]):
            scx_sets[script_of[c]].discard(c)
            for s in scripts:
                scx_sets.setdefault(s, set()).add(c)
    longs = sorted({long_ for _, long_ in sc_values})
    out = [
        header(
            "Unicode data: Script and Script_Extensions",
            "The code points of each Script value (Scripts.txt; Unknown is also every code "
            "point that file does not list) and of each Script_Extensions value: a code "
            "point listed in ScriptExtensions.txt has the scripts listed there, any other "
            "code point its Script.",
            [],
        )
    ]
    for v in longs:
        out.append(
            f"/-- Script={v}. -/\ndef Script.{ident(v)} : List (Nat × Nat) := "
            + lean_ranges(ranges_of(sc_sets.get(v, set())))
            + "\n"
        )
    for v in longs:
        out.append(
            f"/-- Script_Extensions={v}. -/\ndef ScriptExtensions.{ident(v)} : List (Nat × Nat) := "
            + lean_ranges(ranges_of(scx_sets.get(v, set())))
            + "\n"
        )
    out.append("end Unicode\n")
    files["Unicode/Gen/Scripts.lean"] = "\n".join(out)

    # Binary properties
    sets = binary_sets(data)
    binary = sorted(sets)
    ranges = {p: ranges_of(sets[p]) for p in binary}
    # Three files of about the same size.
    parts: list[list[str]] = [[], [], []]
    sizes = [0, 0, 0]
    for p in sorted(binary, key=lambda p: -len(ranges[p])):
        i = sizes.index(min(sizes))
        parts[i].append(p)
        sizes[i] += len(ranges[p])
    for i, props in enumerate(parts, 1):
        props.sort()
        out = [
            header(
                f"Unicode data: binary properties ({i} of 3)",
                "The code points of the binary properties "
                + ", ".join(props)
                + " (PropList.txt, DerivedCoreProperties.txt, extracted/DerivedBinaryProperties.txt, "
                "DerivedNormalizationProps.txt, emoji/emoji-data.txt).",
                [],
            )
        ]
        for p in props:
            out.append(f"/-- {p}. -/\ndef Binary.{ident(p)} : List (Nat × Nat) := " + lean_ranges(ranges[p]) + "\n")
        out.append("end Unicode\n")
        files[f"Unicode/Gen/BinaryProperties{i}.lean"] = "\n".join(out)

    # Sequence types
    seqs = sequence_sets(data)
    out = [
        header(
            "Unicode data: emoji sequences",
            "The sequences of each type of emoji/emoji-sequences.txt and "
            "emoji/emoji-zwj-sequences.txt: the code points that are sequences of one, as "
            "ranges, and the sequences of two or more code points.",
            [],
        )
    ]
    for p in seqs:
        singles = ranges_of(s[0] for s in seqs[p] if len(s) == 1)
        longer = sorted({tuple(s) for s in seqs[p] if len(s) > 1})
        out.append(
            f"/-- {p}: the one-code-point sequences, as ranges. -/\n"
            f"def Strings.{ident(p)}.ranges : List (Nat × Nat) := " + lean_ranges(singles) + "\n"
        )
        out.append(
            f"/-- {p}: the sequences of two or more code points. -/\n"
            f"def Strings.{ident(p)}.strings : List (List Nat) := " + lean_sequences(longer) + "\n"
        )
    out.append("end Unicode\n")
    files["Unicode/Gen/EmojiSequences.lean"] = "\n".join(out)
    files["Unicode/Gen/Classes.lean"] = CLASSES.format(
        version=VERSION,
        id_start=lean_ranges(ranges["ID_Start"]),
        id_continue=lean_ranges(ranges["ID_Continue"]),
        space_separator=lean_ranges(ranges_of(listed["Space_Separator"])),
    )

    # General_Category's and Script's values
    gc_longs = list(dict.fromkeys(l for _, l in gc_values))
    out = [
        header(
            "Unicode data: the values of General_Category and Script",
            "The canonical (long) values of General_Category and Script "
            "(PropertyValueAliases.txt) as inductive types, the values and value aliases "
            "with the constructors they denote, and the total functions from the values to "
            "their code points: a General_Category value that groups others (such as L = "
            "Ll | Lm | Lo | Lt | Lu) is the concatenation of the values it groups.",
            ["Unicode.Gen.GeneralCategory", "Unicode.Gen.Scripts"],
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

    out.append(inductive("GeneralCategoryValue", "The canonical (long) values of General_Category.", gc_longs))
    out.append(inductive("ScriptValue", "The canonical (long) values of Script.", longs))
    out.append(
        "/-- The General_Category values and value aliases, with their long names. -/\n"
        "def GeneralCategory.valueAliases : "
        + pairs("GeneralCategoryValue", [(a, l) for aliases, l in gc_values for a in dict.fromkeys(aliases)])
        + "\n"
    )
    out.append(
        "/-- The Script values and value aliases, with their long names. -/\n"
        "def Script.valueAliases : "
        + pairs("ScriptValue", [(a, l) for aliases, l in sc_values for a in dict.fromkeys(aliases)])
        + "\n"
    )
    arms = []
    for v in gc_longs:
        if v in gc_groups:
            body = " ++ ".join(f"GeneralCategory.{ident(short_to_long[m])}" for m in gc_groups[v])
        else:
            body = f"GeneralCategory.{ident(v)}"
        arms.append(f"  | .{ident(v)} => {body}")
    out.append(
        "/-- The code points whose General_Category is _v_ (for a value that groups others, "
        "the ranges of the values it groups, in turn). -/\n"
        "def GeneralCategoryValue.codePoints : GeneralCategoryValue → List (Nat × Nat)\n" + "\n".join(arms) + "\n"
    )
    out.append(
        "/-- The code points whose Script is _v_. -/\n"
        "def ScriptValue.codePoints : ScriptValue → List (Nat × Nat)\n"
        + "\n".join(f"  | .{ident(v)} => Script.{ident(v)}" for v in longs)
        + "\n"
    )
    out.append(
        "/-- The code points whose Script_Extensions include _v_. -/\n"
        "def ScriptValue.extensionsCodePoints : ScriptValue → List (Nat × Nat)\n"
        + "\n".join(f"  | .{ident(v)} => ScriptExtensions.{ident(v)}" for v in longs)
        + "\n"
    )
    out.append("end Unicode\n")
    files["Unicode/Gen/PropertyValues.lean"] = "\n".join(out)

    # Every property's names and value names
    names = [f for f in data.lines("PropertyAliases.txt")]
    rows: dict[str, list[str]] = {n[0]: [] for n in names}
    for f in data.lines("PropertyValueAliases.txt"):
        values = [f[3], f[1], f[2]] + f[4:] if f[0] == "ccc" else [f[2], f[1]] + f[3:]
        rows[f[0]].append(" ".join(dict.fromkeys(v for v in values if v)))
    rows["scx"] = rows["sc"]
    out = [
        header(
            "Unicode data: every property's names and value names",
            "The names and aliases of each property of PropertyAliases.txt, and the "
            "values and value aliases PropertyValueAliases.txt lists for it "
            "(Script_Extensions has Script's), each row one String of its names "
            "separated by spaces, the long name first.",
            [],
        )
    ]
    out.append(
        "/-- Each property's names and aliases, the short name first. -/\n"
        "def ucdPropertyNames : List (List String) := [\n"
        + ",\n".join("  [" + ", ".join(f'"{a}"' for a in n) + "]" for n in names)
        + "]\n"
    )
    out.append(
        "/-- Each property's short name and value rows (the long name first). -/\n"
        "def ucdPropertyValueRows : List (String × List String) := [\n"
        + ",\n".join(f'  ("{n[0]}", [' + ", ".join(f'"{r}"' for r in rows[n[0]]) + "])" for n in names)
        + "]\n"
    )
    out.append("end Unicode\n")
    files["Unicode/Gen/PropertyValueAliases.lean"] = "\n".join(out)

    return files


def write(files: dict[str, str], check: bool, script: str) -> int:
    """Writes the files (paths under lean/), or with `check` reports the stale ones."""
    stale = []
    for name, text in files.items():
        path = ROOT / "lean" / name
        if check:
            if not path.exists() or path.read_text(encoding="utf-8") != text:
                stale.append(name)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
    if stale:
        print("stale: " + ", ".join(stale) + f" (run python3 {script})", file=sys.stderr)
        return 1
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="exit 1 if a generated file is stale")
    ap.add_argument("--ucd", type=Path, help="the UCD's files (default: $UNICODE_UCD)")
    args = ap.parse_args()
    return write(generate(Data(args.ucd or default_ucd())), args.check, "scripts/unicode_properties.py")


if __name__ == "__main__":
    sys.exit(main())
