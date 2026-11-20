#!/usr/bin/env python3
"""Generate the Unicode data tables of the Unicode library (lean/Unicode).

    python3 scripts/unicode_data.py          # rewrite the generated Lean files (below)
    python3 scripts/unicode_data.py --check  # exit 1 if one is stale
    python3 scripts/unicode_data.py --ucd DIR

The data are the files of the Unicode Character Database 17.0.0, the one
release every generated table of the formalization is read from (DESIGN
§16.9): `ucd/UCD.zip`, which Nix fetches (flake.nix's `ucd`; the dev shell's
UNICODE_UCD, or `--ucd DIR`), checked against its SHA-256 sum by
`scripts/unicode_properties.py`, whose reader this script shares.
Python's `unicodedata` is never used, since its version is the
interpreter's, not the pinned one; the script refuses to run if the archive
is not 17.0.0.

* the full, locale-insensitive case mappings of String.prototype.toLowerCase
  and toUpperCase (§22.1.3.28, §22.1.3.30): the simple mappings of
  UnicodeData.txt (fields 12 and 13), replaced by the unconditional mappings
  of SpecialCasing.txt where it has one;
* the simple and common case foldings of CaseFolding.txt (status C and S:
  scf, for Canonicalize of RegExp in Unicode mode, §22.2.2.7.3);
* for each canonical character, the characters that Canonicalize maps to it
  (the preimages), in Unicode mode (scf) and otherwise (the single-code-unit
  toUppercase rule of §22.2.2.7.3 steps 4–10, with the full uppercase
  mapping above), where they are not just the character itself.

The properties Cased and Case_Ignorable that the context Final_Sigma of
SpecialCasing.txt tests are not generated here: they are the binary property
tables `Unicode.Binary.«Cased»` and `«Case_Ignorable»` of
`scripts/unicode_properties.py`.

These go to lean/Unicode/Gen/CaseData.lean. The data of the Unicode
Normalization Forms (UAX #15) that String.prototype.normalize uses (§22.1.3.15)
go to lean/Unicode/Gen/NormalizationData.lean:

* the Canonical_Combining_Class of each code point whose class is not 0
  (UnicodeData.txt field 3), as runs `(first, last, class)`;
* the full canonical decomposition of each code point that has one: the
  decomposition mappings of UnicodeData.txt (field 5) without a tag, applied
  until none applies, then put in canonical order (UAX #15 §3.3), except the
  Hangul syllables, which are decomposed algorithmically (Unicode §3.12);
* the full compatibility decomposition (every mapping, tagged or not) of
  each code point whose compatibility decomposition is not its canonical one;
* the primary composites: each canonical decomposition mapping of two code
  points whose code point is not Full_Composition_Exclusion
  (DerivedNormalizationProps.txt); the Hangul syllables are again algorithmic.

The mappings are stored as runs `(first, last, stride, delta)`: every
`first + k·stride ≤ last` maps to itself plus `delta`; code points whose
mapping has more than one code point are listed separately.
"""

import argparse
import os
import sys
from pathlib import Path

from unicode_properties import VERSION, Data, default_ucd
from unicode_properties import code_points as ucd_range

# Not resolved: in a Bazel test, the runfiles (whose files link the sources).
ROOT = Path(os.path.abspath(__file__)).parent.parent
OUT = ROOT / "lean" / "Unicode" / "Gen" / "CaseData.lean"
NORMALIZATION_OUT = ROOT / "lean" / "Unicode" / "Gen" / "NormalizationData.lean"


class UCD:
    """The UnicodeData.txt, SpecialCasing.txt, CaseFolding.txt and
    DerivedNormalizationProps.txt facts the tables need."""

    def __init__(self, data: Data):
        for name in ("SpecialCasing.txt", "CaseFolding.txt", "DerivedNormalizationProps.txt"):
            first = data.zip.read(name).decode("utf-8").split("\n", 1)[0]
            if f"-{VERSION}.txt" not in first:
                sys.exit(f"{name} of UCD.zip is not Unicode {VERSION}: {first!r}")
        self.upper: dict[int, int] = {}
        self.lower: dict[int, int] = {}
        self.ccc: dict[int, int] = {}
        self.decomposition: dict[int, tuple[bool, list[int]]] = {}  # (is canonical, mapping)
        for f in data.lines("UnicodeData.txt"):
            cp = int(f[0], 16)
            if f[3] != "0":
                self.ccc[cp] = int(f[3])
            if f[5]:
                parts = f[5].split()
                canonical = not parts[0].startswith("<")
                self.decomposition[cp] = (canonical, [int(x, 16) for x in (parts if canonical else parts[1:])])
            if f[12]:
                self.upper[cp] = int(f[12], 16)
            if f[13]:
                self.lower[cp] = int(f[13], 16)
        self.special_lower: dict[int, list[int]] = {}
        self.special_upper: dict[int, list[int]] = {}
        for f in data.lines("SpecialCasing.txt"):
            if len(f) > 4 and f[4]:
                continue  # a conditional mapping (Final_Sigma, a language)
            cp = int(f[0], 16)
            self.special_lower[cp] = [int(x, 16) for x in f[1].split()]
            self.special_upper[cp] = [int(x, 16) for x in f[3].split()]
        self.scf: dict[int, int] = {}
        for f in data.lines("CaseFolding.txt"):
            if f[1] in ("C", "S"):
                self.scf[int(f[0], 16)] = int(f[2], 16)
        self.full_composition_exclusion: set[int] = set()
        for f in data.lines("DerivedNormalizationProps.txt"):
            if f[1] == "Full_Composition_Exclusion":
                self.full_composition_exclusion.update(ucd_range(f[0]))

    def to_lower(self, cp: int) -> list[int]:
        """The full lowercase mapping (locale-insensitive, unconditional)."""
        if cp in self.special_lower:
            return self.special_lower[cp]
        return [self.lower.get(cp, cp)]

    def to_upper(self, cp: int) -> list[int]:
        """The full uppercase mapping (locale-insensitive, unconditional)."""
        if cp in self.special_upper:
            return self.special_upper[cp]
        return [self.upper.get(cp, cp)]

    def decompose(self, cp: int, compatibility: bool) -> list[int]:
        """The full canonical (or compatibility) decomposition, in canonical order."""

        def go(c: int) -> list[int]:
            d = self.decomposition.get(c)
            if d is None or (not d[0] and not compatibility) or is_hangul_syllable(c):
                return [c]
            return [x for part in d[1] for x in go(part)]

        out = go(cp)
        # Canonical ordering (UAX #15 §3.3): a stable sort of each run of non-starters by class.
        i = 0
        while i < len(out):
            if self.ccc.get(out[i], 0) == 0:
                i += 1
                continue
            j = i
            while j < len(out) and self.ccc.get(out[j], 0) != 0:
                j += 1
            out[i:j] = sorted(out[i:j], key=lambda c: self.ccc.get(c, 0))
            i = j
        return out


def canonicalize_non_unicode(ucd: UCD, cu: int) -> int:
    """Canonicalize (§22.2.2.7.3) steps 4-10 for a code unit."""
    if 0xD800 <= cu <= 0xDFFF:
        return cu
    upper = ucd.to_upper(cu)
    if len(upper) != 1 or upper[0] > 0xFFFF:
        return cu
    mapped = upper[0]
    if cu >= 128 and mapped < 128:
        return cu
    return mapped


def preimages(f, domain):
    classes = {}
    for c in domain:
        classes.setdefault(f(c), []).append(c)
    return {cc: sorted(members) for cc, members in classes.items() if members != [cc]}


def code_points():
    for cp in range(0x110000):
        if 0xD800 <= cp <= 0xDFFF:
            continue
        yield cp


def mapping(f):
    single, multi = {}, {}
    for cp in code_points():
        m = f(cp)
        if m == [cp]:
            continue
        if len(m) == 1:
            single[cp] = m[0] - cp
        else:
            multi[cp] = m
    return single, multi


def runs(single):
    """Greedy runs of equal delta with stride 1 or 2."""
    out = []
    cps = sorted(single)
    i = 0
    while i < len(cps):
        first = cps[i]
        delta = single[first]
        best = (first, 1, i)
        for stride in (1, 2):
            j = i
            last = first
            while j + 1 < len(cps) and cps[j + 1] == last + stride and single[cps[j + 1]] == delta:
                j += 1
                last = cps[j]
            if j > best[2]:
                best = (last, stride, j)
        last, stride, j = best
        out.append((first, last, stride, delta))
        i = j + 1
    return out


def ranges(cps):
    out = []
    for cp in cps:
        if out and out[-1][1] == cp - 1:
            out[-1][1] = cp
        else:
            out.append([cp, cp])
    return out


def lean_list(items, per_line=4):
    lines = []
    for k in range(0, len(items), per_line):
        lines.append("    " + ", ".join(items[k : k + per_line]))
    return "[\n" + ",\n".join(lines) + "]"


def generate(ucd: UCD) -> str:
    lower, lower_multi = mapping(ucd.to_lower)
    upper, upper_multi = mapping(ucd.to_upper)

    def scf(cp):
        return ucd.scf.get(cp, cp)

    fold = {cp: scf(cp) - cp for cp in code_points() if scf(cp) != cp}
    fold_classes = preimages(scf, code_points())
    canon_classes = preimages(lambda cu: canonicalize_non_unicode(ucd, cu), range(0x10000))

    def run_items(rs):
        return [f"⟨0x{a:X}, 0x{b:X}, {s}, {d}⟩" for a, b, s, d in rs]

    def multi_items(m):
        return [f"(0x{cp:X}, [{', '.join(f'0x{x:X}' for x in v)}])" for cp, v in sorted(m.items())]

    def range_items(rs):
        return [f"(0x{a:X}, 0x{b:X})" for a, b in rs]

    return f"""module

@[expose] public section

/-!
# Unicode data: case mappings and case properties

Generated by `scripts/unicode_data.py` from the Unicode Character Database
{VERSION} (do not edit). It holds the locale-insensitive full case mappings
(UnicodeData.txt and the unconditional mappings of SpecialCasing.txt) that
String.prototype.toLowerCase and toUpperCase use (§22.1.3.28, §22.1.3.30),
and the simple case foldings (CaseFolding.txt) and Canonicalize preimages of
RegExp (§22.2.2.7.3). The properties Cased and Case_Ignorable of
SpecialCasing.txt's context Final_Sigma are the binary property tables
`Unicode.Binary.«Cased»` and `«Case_Ignorable»` of the same release.
-/

namespace Unicode

/-- A run of a case mapping: every `first + k × stride ≤ last` maps to itself
plus `delta`. -/
structure CaseRun where
  first : Nat
  last : Nat
  stride : Nat
  delta : Int

/-- The simple lowercase mappings (runs, in code point order). -/
def lowercaseRuns : List CaseRun := {lean_list(run_items(runs(lower)))}

/-- The lowercase mappings to more than one code point. -/
def lowercaseSpecial : List (Nat × List Nat) := {lean_list(multi_items(lower_multi), 2)}

/-- The simple uppercase mappings (runs, in code point order). -/
def uppercaseRuns : List CaseRun := {lean_list(run_items(runs(upper)))}

/-- The uppercase mappings to more than one code point. -/
def uppercaseSpecial : List (Nat × List Nat) := {lean_list(multi_items(upper_multi), 2)}

/-- The simple and common case foldings of CaseFolding.txt (scf), as runs. -/
def simpleCaseFoldingRuns : List CaseRun := {lean_list(run_items(runs(fold)))}

set_option maxRecDepth 20000 in
/-- For each code point that scf maps some other code point to: all the code
points it maps to it (in order), when that is not just the code point itself. -/
def simpleCaseFoldingPreimages : List (Nat × List Nat) := {lean_list(multi_items(fold_classes), 2)}

set_option maxRecDepth 20000 in
/-- For each code unit that Canonicalize maps some other code unit to when
neither the `u` nor the `v` flag is set (§22.2.2.7.3 steps 4–10): all the code
units it maps to it, when that is not just the code unit itself. -/
def canonicalizePreimages : List (Nat × List Nat) := {lean_list(multi_items(canon_classes), 2)}

end Unicode
"""


def is_hangul_syllable(cp):
    return 0xAC00 <= cp <= 0xD7A3


def generate_normalization(ucd: UCD) -> str:
    classes, canonical, compatibility, compositions = [], {}, {}, []
    for cp in code_points():
        if ucd.ccc.get(cp, 0):
            classes.append((cp, ucd.ccc[cp]))
        if is_hangul_syllable(cp):
            continue
        nfd = ucd.decompose(cp, compatibility=False)
        if nfd != [cp]:
            canonical[cp] = nfd
        nfkd = ucd.decompose(cp, compatibility=True)
        if nfkd != nfd:
            compatibility[cp] = nfkd
        d = ucd.decomposition.get(cp)
        if d and d[0] and len(d[1]) == 2 and cp not in ucd.full_composition_exclusion:
            compositions.append((d[1][0], d[1][1], cp))
    class_runs = []
    for cp, k in classes:
        if class_runs and class_runs[-1][1] == cp - 1 and class_runs[-1][2] == k:
            class_runs[-1][1] = cp
        else:
            class_runs.append([cp, cp, k])

    def mapping_items(m):
        return [f"(0x{cp:X}, [{', '.join(f'0x{x:X}' for x in v)}])" for cp, v in sorted(m.items())]

    class_items = [f"(0x{a:X}, 0x{b:X}, {k})" for a, b, k in class_runs]
    composition_items = [f"(0x{a:X}, 0x{b:X}, 0x{c:X})" for a, b, c in sorted(compositions)]
    return f"""module

@[expose] public section

/-!
# Unicode data: the normalization forms

Generated by `scripts/unicode_data.py` from the Unicode Character Database
{VERSION} (do not edit). It holds what the Unicode
Normalization Forms (UAX #15) of String.prototype.normalize (§22.1.3.15)
read: the Canonical_Combining_Class of the code points whose class is not 0,
the full canonical and compatibility decompositions, and the primary
composites. The Hangul syllables are decomposed and composed by the
algorithm of Unicode §3.12 (`Unicode/Normalize.lean`).
-/

namespace Unicode

/-- The Canonical_Combining_Class of the code points whose class is not 0, as
runs `(first, last, class)` in code point order. -/
def combiningClassRuns : List (Nat × Nat × Nat) := {lean_list(class_items, 4)}

set_option maxRecDepth 20000 in
/-- The full canonical decomposition of each code point that has one (the
decomposition mappings of UnicodeData.txt without a tag, applied until none
applies, then put in canonical order), in code point order; the Hangul
syllables are not listed. -/
def canonicalDecompositions : List (Nat × List Nat) := {lean_list(mapping_items(canonical), 2)}

set_option maxRecDepth 40000 in
/-- The full compatibility decomposition of each code point whose
compatibility decomposition is not its canonical decomposition, in code
point order. -/
def compatibilityDecompositions : List (Nat × List Nat) := {lean_list(mapping_items(compatibility), 2)}

set_option maxRecDepth 20000 in
/-- The primary composites `(first, second, composite)`, in the order of
`first` and then `second`: the canonical decomposition mappings of two code
points that are not excluded from composition. -/
def primaryComposites : List (Nat × Nat × Nat) := {lean_list(composition_items, 3)}

end Unicode
"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--ucd", type=Path, help="the UCD's files (default: $UNICODE_UCD)")
    args = ap.parse_args()
    ucd = UCD(Data(args.ucd or default_ucd()))
    outputs = [(OUT, generate(ucd)), (NORMALIZATION_OUT, generate_normalization(ucd))]
    if args.check:
        stale = [out for out, text in outputs if not out.exists() or out.read_text() != text]
        for out in stale:
            print(f"{out.relative_to(ROOT)} is stale: run python3 scripts/unicode_data.py", file=sys.stderr)
        return 1 if stale else 0
    for out, text in outputs:
        out.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
