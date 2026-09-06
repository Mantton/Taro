#!/usr/bin/env python3
"""Runtime stress selection must reach every generated test program."""

import unittest
from pathlib import Path
from unittest.mock import patch

import runtime_stress


class RuntimeStressTests(unittest.TestCase):
    def test_release_profile_reaches_std_and_gc_programs(self) -> None:
        commands = []

        def run(command, **kwargs):
            commands.append(command)
            if "--dist-dir" in command:
                compiler = Path(command[command.index("--dist-dir") + 1]) / "bin/taro"
                compiler.parent.mkdir(parents=True)
                compiler.touch()
            if "-o" in command:
                output = Path(command[command.index("-o") + 1])
                output.parent.mkdir(parents=True, exist_ok=True)
                output.touch()

        with (
            patch.object(runtime_stress.sys, "argv", ["runtime_stress.py", "--release", "--workers", "1"]),
            patch.object(runtime_stress, "run_command", side_effect=run),
        ):
            self.assertEqual(runtime_stress.main(), 0)
        programs = [command for command in commands if len(command) > 1 and command[1] in {"test", "run"}]
        self.assertEqual(len(programs), 3)
        for command in programs:
            self.assertIn("--release", command)

    def test_each_program_is_compiled_once_and_runs_in_every_worker_environment(self) -> None:
        calls = []

        def run(command, **kwargs):
            calls.append((command, kwargs.get("env", {}).copy()))
            if "--dist-dir" in command:
                compiler = Path(command[command.index("--dist-dir") + 1]) / "bin/taro"
                compiler.parent.mkdir(parents=True)
                compiler.touch()
            if "-o" in command:
                output = Path(command[command.index("-o") + 1])
                output.parent.mkdir(parents=True, exist_ok=True)
                output.touch()

        with (
            patch.object(runtime_stress.sys, "argv", ["runtime_stress.py", "--workers", "1,2,4,default"]),
            patch.dict(runtime_stress.os.environ, {"TARO_WORKERS": "9", "TARO_GC_STRESS": "0"}),
            patch.object(runtime_stress, "run_command", side_effect=run),
        ):
            self.assertEqual(runtime_stress.main(), 0)

        compilations = [(command, env) for command, env in calls
                        if len(command) > 1 and command[1] in {"test", "run", "build"}]
        self.assertEqual(len(compilations), 3)
        std_build = next(command for command, _ in compilations if command[1] == "test")
        self.assertEqual(std_build[std_build.index("--tag") + 1], "runtime")
        for command, _ in compilations:
            self.assertIn("-o", command)
            binary = command[command.index("-o") + 1]
            executions = [env for executed, env in calls
                          if executed == [binary] or executed == command]
            self.assertEqual([env.get("TARO_WORKERS") for env in executions], ["1", "2", "4", None])
            expected_stress = "0" if command == std_build else "1"
            self.assertTrue(all(env["TARO_GC_STRESS"] == expected_stress for env in executions))

    def test_invalid_workers_are_rejected_before_bootstrap(self) -> None:
        with (
            patch.object(runtime_stress.sys, "argv", ["runtime_stress.py", "--workers", "0"]),
            patch.object(runtime_stress, "run_command") as run,
            self.assertRaises(SystemExit),
        ):
            runtime_stress.main()
        run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
