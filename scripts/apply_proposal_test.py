#!/usr/bin/env python3
"""Tests of scripts/apply_proposal.py on small made-up texts.

    python3 scripts/apply_proposal_test.py [-v]

Each test merges a made-up proposal into the made-up base below and checks the result, the refusals, the
warnings or the figures copied: one test per kind of block, of clause change and of resolution.
"""

import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import apply_proposal as ap

BASE = """<!doctype html>
<emu-clause id="sec-p">
  <h1>Parent</h1>
  <p>Some prose.</p>
  <emu-clause id="sec-a" type="abstract operation">
    <h1>Alpha ( _x_ )</h1>
    <p>Alpha does a thing.</p>
    <emu-alg>
      1. Let _y_ be _x_.
      1. Return Beta(_y_).
    </emu-alg>
    <emu-note>
      <p>A note.</p>
    </emu-note>
  </emu-clause>
  <emu-clause id="sec-b" type="abstract operation">
    <h1>Beta ( _x_ )</h1>
    <emu-alg>
      1. Assert: _x_ is a String.
      1. Return _x_.
    </emu-alg>
  </emu-clause>
  <emu-clause id="sec-c">
    <h1>Gamma</h1>
    <p>See <emu-xref href="#sec-b"></emu-xref>, and Beta(_z_).</p>
    <emu-table id="table-g" caption="Things">
      <table>
        <thead>
          <tr><th>Name</th><th>Meaning</th></tr>
        </thead>
        <tr><td>one</td><td>1</td></tr>
        <tr><td>two</td><td>2</td></tr>
      </table>
    </emu-table>
    <emu-grammar type="definition">
      Thing :
        `a`
        `b`

      Other :
        `c`
    </emu-grammar>
  </emu-clause>
</emu-clause>
"""


def merge(prop, res=""):
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write(res)
    try:
        return ap.merge(BASE, prop, ap.read_resolutions(f.name))
    finally:
        os.unlink(f.name)


def clause(text, cid):
    """The text of clause `cid` in `text`."""
    n = next(n for n in ap.parse_tree(text).walk() if n.id == cid)
    return text[n.open_start:n.close_end]


A_CONTEXT = """    <h1>Alpha ( _x_ )</h1>
    <p>Alpha does a thing.</p>
"""


class Blocks(unittest.TestCase):
    def test_replaced_step_and_the_rest_byte_for_byte(self):
        out, rep = merge(f"""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-a" type="abstract operation">
{A_CONTEXT}    <emu-alg>
      1. Let _y_ be _x_.
      1. Return <del>Beta</del><ins>Delta</ins>(_y_).
    </emu-alg>
  </emu-clause>
</emu-clause>""")
        self.assertEqual(rep["refusals"], [])
        self.assertIn("1. Return Delta(_y_).", clause(out, "sec-a"))
        self.assertNotIn("Beta(_y_)", clause(out, "sec-a"))
        self.assertEqual(out.replace("Return Delta(_y_)", "Return Beta(_y_)"), BASE)
        self.assertEqual(rep["checks"]["ins_missing"], [])
        self.assertTrue(rep["checks"]["tree_ok"])

    def test_context_that_differs_is_refused_and_ignore_answers(self):
        prop = """<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-a" type="abstract operation">
    <h1>Alpha ( _x_ )</h1>
    <p>Alpha does another thing.</p>
  </emu-clause>
</emu-clause>"""
        _, rep = merge(prop)
        self.assertEqual(len(rep["refusals"]), 1)
        self.assertEqual((rep["refusals"][0]["clause"], rep["refusals"][0]["block"]), ("sec-a", 1))
        self.assertIn("context block", rep["refusals"][0]["message"])
        out, rep = merge(prop, "ignore sec-a 1 abbreviated\n")
        self.assertEqual(rep["refusals"], [])
        self.assertEqual(out, BASE)

    def test_old_text_that_differs_is_refused(self):
        _, rep = merge("""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-b" type="abstract operation">
    <h1>Beta ( _x_ )</h1>
    <emu-alg>
      1. Return <del>_x_</del><ins>_x_ + 1</ins>.
    </emu-alg>
  </emu-clause>
</emu-clause>""")
        self.assertEqual(len(rep["refusals"]), 1)
        self.assertIn("old text", rep["refusals"][0]["message"])
        self.assertIn("Assert: _x_ is a String.", rep["refusals"][0]["diff"])

    def test_loose_match_of_punctuation_left_by_an_insertion(self):
        out, rep = merge(f"""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-a" type="abstract operation">
{A_CONTEXT}    <emu-alg>
      1. Let _y_ be _x_.
      1. Return Beta(_y_, <ins>*true*</ins>).
    </emu-alg>
  </emu-clause>
</emu-clause>""")
        self.assertEqual(rep["refusals"], [])
        self.assertIn("Return Beta(_y_, *true*).", out)
        self.assertEqual(rep["log"]["matched_loosely"], ["sec-a block 2 (emu-alg)"])

    def test_inserted_block_after_its_predecessor(self):
        out, rep = merge(f"""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-a" type="abstract operation">
{A_CONTEXT}    <ins class="block"><p>A new paragraph.</p></ins>
    <emu-alg>
      1. Let _y_ be _x_.
      1. Return Beta(_y_).
    </emu-alg>
  </emu-clause>
</emu-clause>""")
        self.assertEqual(rep["refusals"], [])
        a = clause(out, "sec-a")
        self.assertLess(a.index("Alpha does a thing."), a.index("A new paragraph."))
        self.assertLess(a.index("A new paragraph."), a.index("<emu-alg>"))

    def test_insertion_among_omitted_blocks_is_refused_and_place_answers(self):
        prop = """<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-a" type="abstract operation">
    <h1>Alpha ( _x_ )</h1>
    <ins class="block"><p>Placed.</p></ins>
  </emu-clause>
</emu-clause>"""
        _, rep = merge(prop)
        self.assertEqual(len(rep["refusals"]), 1)
        self.assertIn("place sec-a 1 after N", rep["refusals"][0]["message"])
        out, rep = merge(prop, "place sec-a 1 after 2\n")
        self.assertEqual(rep["refusals"], [])
        a = clause(out, "sec-a")
        self.assertLess(a.index("</emu-alg>"), a.index("Placed."))
        self.assertLess(a.index("Placed."), a.index("<emu-note>"))


class Clauses(unittest.TestCase):
    def test_new_clause_after_its_previous_sibling(self):
        out, rep = merge("""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-a" type="abstract operation">
    <h1>Alpha ( _x_ )</h1>
  </emu-clause>
  <emu-clause id="sec-new" type="abstract operation">
    <h1><ins>Epsilon ( )</ins></h1>
    <emu-alg>
      1. Return *true*.
    </emu-alg>
  </emu-clause>
</emu-clause>""")
        self.assertEqual(rep["refusals"], [])
        ids = [n.id for n in ap.parse_tree(out).walk() if n.id]
        self.assertEqual(ids, ["sec-p", "sec-a", "sec-new", "sec-b", "sec-c"])
        self.assertIn("<h1>Epsilon ( )</h1>", out)
        self.assertNotIn("<ins>", out)
        self.assertTrue(rep["checks"]["tree_ok"])

    def test_removed_clause_warns_of_its_name_and_rename_answers(self):
        prop = """<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-a" type="abstract operation">
    <h1>Alpha ( _x_ )</h1>
    <p>Alpha does a thing.</p>
    <emu-alg>
      1. Let _y_ be _x_.
      1. Return <del>Beta</del><ins>Delta</ins>(_y_).
    </emu-alg>
  </emu-clause>
  <emu-clause id="del-sec-b"></emu-clause>
  <emu-clause id="sec-d" type="abstract operation" oldids="sec-b">
    <h1><ins>Delta ( _x_ )</ins></h1>
    <emu-alg>
      1. Return _x_.
    </emu-alg>
  </emu-clause>
</emu-clause>"""
        out, rep = merge(prop)
        self.assertEqual(rep["refusals"], [])
        self.assertEqual(rep["log"]["removed"], ["sec-b"])
        self.assertNotIn('id="sec-b"', out)
        self.assertEqual(len(rep["warnings"]), 1)
        self.assertIn("Beta (sec-b, removed (sec-b)) is still used in 1 clause(s): sec-c", rep["warnings"][0])
        out, rep = merge(prop, "rename Beta Delta the proposal's new name\n")
        self.assertEqual(rep["warnings"], [])
        self.assertIn("and Delta(_z_)", out)
        self.assertEqual(rep["log"]["renamed"], ["Beta -> Delta: 1 occurrence(s) left by the proposal"])

    def test_link_to_a_removed_clause_warns_unless_an_oldid_keeps_it(self):
        prop = """<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-b" type="abstract operation">
    <h1><del>Beta ( _x_ )</del></h1>
  </emu-clause>
</emu-clause>"""
        out, rep = merge(prop)
        self.assertEqual(rep["refusals"], [])
        self.assertNotIn('id="sec-b"', out)
        self.assertTrue(any('href="#sec-b"' in w for w in rep["warnings"]))

    def test_new_attributes_are_added(self):
        out, rep = merge("""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-c" oldids="sec-gamma" number="9">
    <h1>Gamma</h1>
  </emu-clause>
</emu-clause>""")
        self.assertEqual(rep["refusals"], [])
        self.assertIn('<emu-clause id="sec-c" oldids="sec-gamma">', out)
        self.assertNotIn("number=", out)


class Rebase(unittest.TestCase):
    # the base gained the Assert after the proposal was written; the proposal changes the Return step
    PROP = """<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-b" type="abstract operation">
    <h1>Beta ( _x_ )</h1>
    <emu-alg>
      1. Return <del>_x_</del><ins>_x_ + 1</ins>.
    </emu-alg>
  </emu-clause>
</emu-clause>"""

    def test_newer_base_is_refused(self):
        _, rep = merge(self.PROP)
        self.assertEqual(len(rep["refusals"]), 1)

    def test_rebase_keeps_the_base_on_unmarked_lines(self):
        out, rep = merge(self.PROP, "rebase sec-b 1 base gained an Assert\n")
        self.assertEqual(rep["refusals"], [])
        b = clause(out, "sec-b")
        self.assertIn("1. Assert: _x_ is a String.\n      1. Return _x_ + 1.", b)

    def test_rebase_take_takes_the_proposal_on_unmarked_lines(self):
        # the proposal also rewrites the Assert without marking it
        prop = self.PROP.replace("      1. Return <del>", "      1. Assert: _x_ is a String value.\n      1. Return <del>")
        out, rep = merge(prop, "rebase sec-b 1\n")
        self.assertEqual(rep["refusals"], [])
        self.assertIn("1. Assert: _x_ is a String.\n      1. Return _x_ + 1.", clause(out, "sec-b"))
        out, rep = merge(prop, "rebase-take sec-b 1 unmarked change\n")
        self.assertEqual(rep["refusals"], [])
        self.assertIn("1. Assert: _x_ is a String value.\n      1. Return _x_ + 1.", clause(out, "sec-b"))

    def test_use_new_keep_base_and_patch(self):
        prop = """<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-b" type="abstract operation">
    <h1>Beta ( _x_ )</h1>
    <emu-alg>
      1. Return <del>_x_</del><ins>_x_ + 1</ins>.
    </emu-alg>
  </emu-clause>
</emu-clause>"""
        out, rep = merge(prop, "use-new sec-b 1\n")
        self.assertEqual(rep["refusals"], [])
        self.assertNotIn("Assert", clause(out, "sec-b"))
        self.assertIn("Return _x_ + 1.", out)
        out, rep = merge(prop, "keep-base sec-b 1\n")
        self.assertEqual((rep["refusals"], out), ([], BASE))
        out, rep = merge(prop, 'patch sec-b 1 "Return _x_." ==> "Return _x_ + 1."\n')
        self.assertEqual(rep["refusals"], [])
        self.assertIn("Assert: _x_ is a String.\n      1. Return _x_ + 1.", out)


class TablesAndGrammars(unittest.TestCase):
    def test_table_merged_row_by_row(self):
        out, rep = merge("""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-c">
    <h1>Gamma</h1>
    <p>See <emu-xref href="#sec-b"></emu-xref>, and Beta(_z_).</p>
    <emu-table id="table-g" caption="Things">
      <table>
        <tr><th>Name</th><th>Meaning</th></tr>
        <tr><td>one</td><td><del>1</del><ins>one</ins></td></tr>
        <tr><td><ins>one and a half</ins></td><td><ins>1.5</ins></td></tr>
        <tr><td>two</td><td>2</td></tr>
      </table>
    </emu-table>
  </emu-clause>
</emu-clause>""")
        self.assertEqual(rep["refusals"], [])
        c = clause(out, "sec-c")
        self.assertIn("<thead>", c)
        self.assertIn("<tr><td>one</td><td>one</td></tr>", c)
        self.assertLess(c.index("one and a half"), c.index("<td>two</td>"))

    def test_grammar_merged_rule_by_rule(self):
        out, rep = merge("""<emu-clause id="sec-p"><h1>Parent</h1>
  <emu-clause id="sec-c">
    <h1>Gamma</h1>
    <emu-grammar type="definition">
      Thing :
        `a`
        `b`
        <ins>`b` `b`</ins>
    </emu-grammar>
  </emu-clause>
</emu-clause>""", "ignore sec-c 1 abbreviated\n")
        self.assertEqual(rep["refusals"], [])
        c = clause(out, "sec-c")
        self.assertIn("        `b`\n        `b` `b`\n\n      Other :", c)


class Figures(unittest.TestCase):
    def test_new_figures_copied_and_the_base_s_kept(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            for sub, name, body in (("prop", "new.svg", "N"), ("prop", "old.svg", "P"), ("base", "old.svg", "B")):
                (d / sub / "img").mkdir(parents=True, exist_ok=True)
                (d / sub / "img" / name).write_text(body)
            (d / "out").mkdir()
            out = '<img src="img/new.svg"><img src="img/old.svg"><img src="img/gone.svg">'
            copied, problems = ap.copy_images(d / "prop", d / "out", out, d / "base")
            self.assertEqual(copied, ["new.svg"])
            self.assertEqual((d / "out" / "img" / "new.svg").read_text(), "N")
            self.assertFalse((d / "out" / "img" / "old.svg").exists())
            self.assertEqual(len(problems), 2)
            self.assertIn("img/gone.svg", problems[0])
            self.assertIn("the base's is kept", problems[1])


if __name__ == "__main__":
    unittest.main()
