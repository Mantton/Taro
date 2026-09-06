#!/usr/bin/env python3
"""The development launcher owns only options before its input path."""

import unittest
from unittest.mock import patch

import run_dist


class RunDistributionTests(unittest.TestCase):
    def test_program_test_argument_is_forwarded_unchanged(self) -> None:
        with (
            patch.object(run_dist.sys, "argv", ["run_dist.py", "program.tr", "--", "--test"]),
            patch.object(run_dist.subprocess, "run") as run,
        ):
            run_dist.main()
        self.assertEqual(run.call_args.args[0][1:], ["run", "program.tr", "--", "--test"])

    def test_invalid_invocation_does_not_build_a_distribution(self) -> None:
        for arguments in ([], ["--test", "program.tr", "unexpected"]):
            with (
                self.subTest(arguments=arguments),
                patch.object(run_dist.sys, "argv", ["run_dist.py", *arguments]),
                patch.object(run_dist.subprocess, "run") as run,
                self.assertRaises(SystemExit),
            ):
                run_dist.main()
            run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
