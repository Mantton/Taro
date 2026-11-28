#!/usr/bin/env python3
"""Distribution publication must preserve the last usable toolchain on failure."""

import argparse
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import build_dist


class BuildDistributionTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.repo = self.root / "repo"
        self.std = self.repo / "std"
        self.std.mkdir(parents=True)
        (self.repo / "runtime").mkdir()
        (self.repo / "runtime/GO-LICENSE").write_text("Go runtime attribution")
        target = self.repo / "target/release"
        target.mkdir(parents=True)
        (target / "taro-bin").write_bytes(b"new compiler")
        (target / "libtaro_runtime.a").write_bytes(b"new runtime")
        self.dist = self.repo / "dist"
        self.dist.mkdir()
        (self.dist / "usable").write_text("old toolchain", encoding="utf-8")

    def build(self, command_runner, dist=None, *, sdk=False, llvm_prefix=None) -> None:
        args = argparse.Namespace(
            profile="release", dist_dir=dist or self.dist, std_path=self.std,
            target=None, sdk=sdk, llvm_prefix=llvm_prefix,
        )
        with (
            patch.object(build_dist, "__file__", str(self.repo / "development/scripts/build_dist.py")),
            patch.object(build_dist, "parse_args", return_value=args),
            patch.object(build_dist, "run_command", side_effect=command_runner),
            patch.object(build_dist.disk_guard, "enforce"),
        ):
            build_dist.main()

    def test_bootstrap_failure_preserves_existing_distribution(self) -> None:
        def fail_bootstrap(command, **kwargs):
            if "check" in command:
                raise subprocess.CalledProcessError(1, command)

        with self.assertRaises(subprocess.CalledProcessError):
            self.build(fail_bootstrap)
        self.assertEqual((self.dist / "usable").read_text(), "old toolchain")

    def test_symlink_destination_is_rejected_before_building(self) -> None:
        link = self.repo / "linked-dist"
        link.symlink_to(self.dist, target_is_directory=True)
        calls = []
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.build(lambda command, **kwargs: calls.append(command), dist=link)
        self.assertEqual(calls, [])
        self.assertEqual((self.dist / "usable").read_text(), "old toolchain")

    def test_regular_file_destination_is_rejected_before_building(self) -> None:
        destination = self.repo / "important-file"
        destination.write_text("keep this", encoding="utf-8")
        calls = []
        with self.assertRaisesRegex(ValueError, "directory"):
            self.build(lambda command, **kwargs: calls.append(command), dist=destination)
        self.assertEqual(calls, [])
        self.assertEqual(destination.read_text(), "keep this")

    def test_success_publishes_complete_distribution_once(self) -> None:
        def bootstrap(command, **kwargs):
            if "target-facts" in command:
                Path(command[-1]).write_text('triple = "test"\npointer_bits = 64\n')
            if "check" in command:
                self.assertEqual((self.dist / "usable").read_text(), "old toolchain")
                home = Path(kwargs["env"]["TARO_HOME"])
                (home / "attached-std").write_text("ready", encoding="utf-8")

        self.build(bootstrap)
        self.assertFalse((self.dist / "usable").exists())
        self.assertEqual((self.dist / "bin/taro").read_bytes(), b"new compiler")
        self.assertEqual((self.dist / "attached-std").read_text(), "ready")
        self.assertIn("pointer_bits = 64", (self.dist / "lib/taro/runtime/target-facts.toml").read_text())
        self.assertEqual((self.dist / "std").resolve(), self.std)
        self.assertFalse((self.dist / ".std_bootstrap.tr").exists())

    def test_publication_failure_restores_previous_distribution(self) -> None:
        rename = Path.rename

        def fail_publication(source, target):
            if source.name == "dist" and source.parent != self.repo:
                raise OSError("publication failed")
            return rename(source, target)

        with patch.object(Path, "rename", fail_publication):
            with self.assertRaisesRegex(OSError, "publication failed"):
                self.build(lambda command, **kwargs: None)
        self.assertEqual((self.dist / "usable").read_text(), "old toolchain")

    def test_sdk_bootstraps_against_its_copied_std(self) -> None:
        (self.std / "src").mkdir()
        (self.std / "src/example.tr").write_text("func example() {}")
        (self.std / "package.toml").write_text("[package]\n")
        (self.std / "package.lock").write_text("version = 1\n")
        (self.std / "target").mkdir()
        (self.std / "target/cache").write_text("local cache")
        sdk_target = self.repo / "target/sdk/release"
        sdk_target.mkdir(parents=True)
        (sdk_target / "taro-bin").write_bytes(b"sdk compiler")
        (sdk_target / "libtaro_runtime.a").write_bytes(b"sdk runtime")
        (sdk_target / "taro-lsp").write_bytes(b"language server")
        for name in ("LICENSE-MIT", "LICENSE-APACHE"):
            (self.repo / name).write_text(name)
        llvm = self.portable_llvm()
        commands = []

        def inspect(command, **kwargs):
            commands.append(command)
            if command[0] == "cargo":
                self.assertEqual(kwargs["env"]["LLVM_SYS_221_PREFIX"], str(llvm))
                self.assertEqual(kwargs["env"]["CARGO_TARGET_DIR"], str(self.repo / "target/sdk"))
            if "check" in command:
                staged = Path(kwargs["env"]["TARO_HOME"])
                self.assertEqual(command[command.index("--std-path") + 1], str(staged / "std"))
                self.assertFalse((staged / "std").is_symlink())
                self.assertFalse((staged / "std/target").exists())

        with (
            patch.object(build_dist.sys, "platform", "darwin"),
            patch.object(build_dist, "apple_build_env", return_value=None),
            patch.object(build_dist, "verify_sdk_binary") as audit,
            patch.object(build_dist, "host_rust_target", return_value="aarch64-apple-darwin"),
            patch.object(build_dist.third_party_notices, "render", return_value="notices") as notices,
        ):
            self.build(inspect, sdk=True, llvm_prefix=llvm)
        self.assertEqual([call.args[0].name for call in audit.call_args_list], ["taro", "taro-lsp"])
        self.assertEqual(notices.call_args.args[2], llvm / "LICENSE.TXT")
        self.assertEqual((self.dist / "THIRD_PARTY_NOTICES").read_text(), "notices")
        self.assertEqual((self.dist / "LICENSE-MIT").read_text(), "LICENSE-MIT")
        self.assertEqual((self.dist / "bin/taro").read_bytes(), b"sdk compiler")
        self.assertIn("--locked", next(command for command in commands if "taro-lsp" in command))
        (self.std / "src/example.tr").unlink()
        self.assertTrue((self.dist / "std/src/example.tr").is_file())
        self.assertTrue((self.dist / "std/package.lock").is_file())
        self.assertEqual((self.dist / "bin/taro-lsp").read_bytes(), b"language server")

    def portable_llvm(self) -> Path:
        llvm = self.root / "llvm"
        (llvm / "bin").mkdir(parents=True)
        (llvm / "bin/llvm-config").write_text("")
        (llvm / "taro-llvm.json").write_text("{}")
        (llvm / "LICENSE.TXT").write_text("LLVM license")
        return llvm

    def test_sdk_requires_a_portable_llvm(self) -> None:
        with patch.object(build_dist.sys, "platform", "linux"):
            with self.assertRaisesRegex(ValueError, "--llvm-prefix"):
                self.build(lambda command, **kwargs: None, sdk=True)
            homebrew = self.root / "homebrew-llvm"
            (homebrew / "bin").mkdir(parents=True)
            (homebrew / "bin/llvm-config").write_text("")
            with self.assertRaisesRegex(ValueError, "not an LLVM installation from build_llvm.py"):
                self.build(lambda command, **kwargs: None, sdk=True, llvm_prefix=homebrew)
        self.assertEqual((self.dist / "usable").read_text(), "old toolchain")

    def test_macos_floor_matches_the_compiler(self) -> None:
        source = (Path(__file__).resolve().parents[2] / "compiler/src/codegen/target.rs").read_text()
        self.assertIn(
            f'pub const MACOS_DEPLOYMENT_TARGET: &str = "{build_dist.MACOS_DEPLOYMENT_TARGET}";', source
        )
        import build_llvm
        self.assertEqual(build_llvm.MACOS_DEPLOYMENT_TARGET, build_dist.MACOS_DEPLOYMENT_TARGET)

    def test_macos_floor_audit_rejects_newer_minimum(self) -> None:
        commands = "Load command 9\n      cmd LC_BUILD_VERSION\n    minos 26.0\n      sdk 27.2\n"
        with patch.object(build_dist.subprocess, "check_output", return_value=commands):
            with self.assertRaisesRegex(ValueError, "requires macOS \\['26.0'\\]"):
                build_dist.verify_macos_floor(Path("taro"))
        with patch.object(build_dist.subprocess, "check_output", return_value=commands.replace("26.0", "14.0")):
            build_dist.verify_macos_floor(Path("taro"))

    def linux_audit(self, dynamic: str, versions: str) -> None:
        outputs = {"--dynamic": dynamic, "--version-info": versions}
        with patch.object(
            build_dist.subprocess, "check_output",
            side_effect=lambda command, **kwargs: outputs[command[1]],
        ):
            build_dist.verify_linux_linkage(Path("taro"))

    def test_linux_audit_accepts_core_system_libraries(self) -> None:
        self.linux_audit(
            " 0x1 (NEEDED) Shared library: [libc.so.6]\n 0x1 (NEEDED) Shared library: [libstdc++.so.6]\n",
            "  0x0010:   Name: GLIBC_2.17  Flags: none\n  0x0020:   Name: GLIBC_2.28\n"
            "  0x0030:   Name: GLIBCXX_3.4.25  Flags: none\n",
        )

    def test_linux_audit_rejects_non_system_library_and_new_glibc(self) -> None:
        with self.assertRaisesRegex(ValueError, "non-system library: libzstd.so.1"):
            self.linux_audit(" 0x1 (NEEDED) Shared library: [libzstd.so.1]\n", "")
        with self.assertRaisesRegex(ValueError, "unexpected library search path"):
            self.linux_audit(" 0x1d (RUNPATH) Library runpath: [/opt/llvm/lib]\n", "")
        with self.assertRaisesRegex(ValueError, "requires GLIBC_2.34"):
            self.linux_audit("", "  0x0010:   Name: GLIBC_2.34  Flags: none\n")
        with self.assertRaisesRegex(ValueError, "requires GLIBCXX_3.4.30"):
            self.linux_audit("", "  0x0010:   Name: GLIBCXX_3.4.30  Flags: none\n")

    def test_linkage_audit_rejects_homebrew_library(self) -> None:
        dependencies = "taro:\n\t/opt/homebrew/lib/libssl.4.dylib (compatibility version 4.0)\n"
        with patch.object(build_dist.subprocess, "check_output", return_value=dependencies):
            with self.assertRaisesRegex(ValueError, "non-system library"):
                build_dist.verify_macos_linkage(Path("taro"))

    def test_failed_restore_retains_the_previous_distribution_for_recovery(self) -> None:
        rename = Path.rename

        def fail_publication_and_restore(source, target):
            if source.parent != self.repo:
                raise OSError("rename failed")
            return rename(source, target)

        with patch.object(Path, "rename", fail_publication_and_restore):
            with self.assertRaisesRegex(OSError, "rename failed"):
                self.build(lambda command, **kwargs: None)
        saved = list(self.repo.glob(".dist-*/previous/usable"))
        self.assertEqual(len(saved), 1)
        self.assertEqual(saved[0].read_text(), "old toolchain")


if __name__ == "__main__":
    unittest.main()
