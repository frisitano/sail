"""Unit tests for the Sail mkdocstrings handler (no MkDocs build needed).

Run from the mkdocstrings-sail directory with any interpreter that has the
package's dependencies, e.g.:

    uv run --with . python -m unittest discover tests
"""

from __future__ import annotations

import unittest

from mkdocstrings_handlers.sail import Bundle, BundleError, anchor_for
from mkdocstrings_handlers.sail._handler import _highlight_linked

# Shaped exactly like sail --doc --doc-format identity --doc-embed plain
# --doc-embed-with-location output (loc = [line1, bol1, char1, line2, bol2, char2]).
BUNDLE = {
    "version": 1,
    "embedding": "plain",
    "functions": {
        "step": {
            "function": {
                "number": 0,
                "source": {
                    "contents": "function step() = {\n    PC = increment(PC)\n}",
                    "file": "spec/core/machine.sail",
                    "loc": [7, 122, 122, 9, 165, 166],
                },
                "comment": " Advance the machine. ",
            },
            "links": [
                {"type": "register", "id": "PC", "file": "spec/core/machine.sail", "loc": [146, 148]},
                {"type": "function", "id": "increment", "file": "spec/core/machine.sail", "loc": [151, 160]},
                {"type": "register", "id": "PC", "file": "spec/core/machine.sail", "loc": [161, 163]},
            ],
        },
        "increment": {
            "function": {
                "number": 0,
                "source": "function increment(w) = w",
            }
        },
    },
    "vals": {
        "increment": {
            "val": {
                "source": {
                    "contents": "val increment : word -> word",
                    "file": "spec/lib/util.sail",
                    "loc": [9, 129, 129, 9, 129, 157],
                },
                "comment": " Increment a word. ",
            }
        }
    },
    "types": {
        "word": {
            "type": {
                "contents": "type word = bits(8)",
                "file": "spec/lib/util.sail",
                "loc": [6, 74, 74, 6, 74, 93],
            },
            "comment": " The machine word type. ",
        }
    },
    "mappings": {
        "flag_bit": [
            {
                "number": 0,
                "source": "flag_bit : bool <-> bits(1) = {true <-> 0b1, false <-> 0b0}",
            }
        ]
    },
    "lets": {
        # a function-typed link whose id is only a mapping must retarget
        "uses_mapping": {
            "let": {
                "source": {
                    "contents": "let x = flag_bit(true)",
                    "file": "spec/core/machine.sail",
                    "loc": [12, 200, 200, 12, 200, 222],
                }
            },
            "links": [
                {"type": "function", "id": "flag_bit", "file": "spec/core/machine.sail", "loc": [208, 216]},
            ],
        }
    },
}


class TestBundle(unittest.TestCase):
    def setUp(self):
        self.bundle = Bundle(dict(BUNDLE))

    def test_anchor_scheme_matches_mkdocs_target(self):
        self.assertEqual(anchor_for("function", "step"), "function-step")
        self.assertEqual(anchor_for("function", "operator +"), "function-operator--")

    def test_find_prefers_function_over_val(self):
        self.assertEqual(self.bundle.find("increment").kind, "function")
        self.assertEqual(self.bundle.find("increment", kind="val").kind, "val")

    def test_find_unknown_raises(self):
        with self.assertRaises(BundleError):
            self.bundle.find("nonexistent")

    def test_version_check(self):
        with self.assertRaises(BundleError):
            Bundle({"version": 2})

    def test_comment_and_clauses(self):
        step = self.bundle.find("step")
        self.assertEqual(step.comment, " Advance the machine. ")
        self.assertEqual(len(step.clauses), 1)
        self.assertTrue(step.clauses[0].text.startswith("function step()"))

    def test_link_offsets_are_relative_and_in_range(self):
        step = self.bundle.find("step")
        clause = step.clauses[0]
        links = clause.links_within(step.links)
        self.assertEqual(len(links), 3)
        for start, end, anchor in links:
            self.assertEqual(clause.text[start:end], {"register-PC": "PC", "function-increment": "increment"}[anchor])

    def test_type_comment_from_sibling_key(self):
        word = self.bundle.find("word")
        self.assertEqual(word.comment, " The machine word type. ")

    def test_mapping_application_link_retargets(self):
        uses = self.bundle.find("uses_mapping")
        self.assertEqual([l.kind for l in uses.links], ["mapping"])
        self.assertEqual(uses.links[0].anchor, "mapping-flag_bit")
        clause = uses.clauses[0]
        (start, end, anchor) = clause.links_within(uses.links)[0]
        self.assertEqual(clause.text[start:end], "flag_bit")

    def test_raw_source_has_no_links(self):
        increment = self.bundle.find("increment")
        clause = increment.clauses[0]
        self.assertIsNone(clause.start)
        self.assertEqual(clause.links_within(increment.links), [])


class TestHighlightLinked(unittest.TestCase):
    def test_autorefs_wrap_exact_spans(self):
        step = Bundle(dict(BUNDLE)).find("step")
        clause = step.clauses[0]
        html = _highlight_linked(clause.text, clause.links_within(step.links))
        self.assertIn('<autoref identifier="function-increment" optional>', html)
        self.assertEqual(html.count('<autoref identifier="register-PC" optional>'), 2)
        self.assertEqual(html.count("</autoref>"), 3)
        # keyword highlighting from the Sail lexer survives alongside the links
        self.assertIn('<span class="k">function</span>', html)

    def test_html_is_escaped(self):
        html = _highlight_linked('let s = "a <b> & c"', [])
        self.assertNotIn("<b>", html)
        self.assertIn("&lt;b&gt;", html)


if __name__ == "__main__":
    unittest.main()
