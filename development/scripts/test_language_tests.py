#!/usr/bin/env python3
"""Regression tests for language-test directives."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from language_tests import parse_test_directives


class LanguageTestDirectiveTests(unittest.TestCase):
    def test_stdin_is_decoded_from_a_json_string(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "stdin.tr"
            source.write_text('// STDIN: "first line\\nsecond line\\n"\n', encoding="utf-8")

            directives = parse_test_directives(source)

            self.assertEqual(directives["stdin"], "first line\nsecond line\n")


if __name__ == "__main__":
    unittest.main()
