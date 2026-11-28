#!/bin/sh
# Install the Taro SDK for macOS (Apple Silicon) or Linux (x86-64, ARM64).
#
#   curl -fsSL https://raw.githubusercontent.com/Mantton/Taro/main/install.sh | sh
#
# Environment:
#   TARO_VERSION          release tag to install, e.g. v0.1.0 (default: newest release)
#   TARO_INSTALL          installation root (default: ~/.taro)
#   TARO_NO_MODIFY_PATH   set to 1 to leave shell startup files unchanged
#   TARO_DOWNLOAD_URL     base URL holding the release files (default: GitHub releases)
#
# The SDK is unpacked into $TARO_INSTALL/toolchains/<name>, and
# $TARO_INSTALL/current points at it. Rerun the script to upgrade; remove
# $TARO_INSTALL and the PATH line it added to uninstall.

set -eu

REPOSITORY="Mantton/Taro"

say() { printf 'taro-install: %s\n' "$*"; }
fail() { printf 'taro-install: error: %s\n' "$*" >&2; exit 1; }
need() { command -v "$1" >/dev/null 2>&1 || fail "'$1' is required but was not found"; }

detect_platform() {
    os=$(uname -s)
    machine=$(uname -m)
    case "$os" in
        Darwin)
            # A shell running under Rosetta reports x86_64 on Apple Silicon.
            if [ "$machine" = x86_64 ] && [ "$(sysctl -n sysctl.proc_translated 2>/dev/null || echo 0)" = 1 ]; then
                machine=arm64
            fi
            [ "$machine" = arm64 ] || fail "Taro currently supports Apple Silicon Macs only"
            echo macos-arm64
            ;;
        Linux)
            case "$machine" in
                x86_64 | amd64) echo linux-x86_64 ;;
                aarch64 | arm64) echo linux-arm64 ;;
                *) fail "unsupported Linux architecture: $machine" ;;
            esac
            ;;
        *) fail "unsupported operating system: $os (Taro supports macOS and Linux)" ;;
    esac
}

latest_tag() {
    # Releases are listed newest first, including previews.
    curl -fsSL "https://api.github.com/repos/$REPOSITORY/releases?per_page=1" \
        | sed -n 's/.*"tag_name": *"\([^"]*\)".*/\1/p' | head -n 1
}

sha256() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | cut -d ' ' -f 1
    else
        shasum -a 256 "$1" | cut -d ' ' -f 1
    fi
}

add_to_path() {
    bin="$1"
    [ "${TARO_NO_MODIFY_PATH:-0}" = 1 ] && return 1
    case "${SHELL:-}" in
        */zsh) profile="${ZDOTDIR:-$HOME}/.zshrc"; line="export PATH=\"$bin:\$PATH\"" ;;
        */bash)
            if [ "$(uname -s)" = Darwin ]; then profile="$HOME/.bash_profile"; else profile="$HOME/.bashrc"; fi
            line="export PATH=\"$bin:\$PATH\""
            ;;
        */fish)
            profile="${XDG_CONFIG_HOME:-$HOME/.config}/fish/conf.d/taro.fish"
            line="fish_add_path \"$bin\""
            mkdir -p "$(dirname "$profile")"
            ;;
        *) profile="$HOME/.profile"; line="export PATH=\"$bin:\$PATH\"" ;;
    esac
    if [ -f "$profile" ] && grep -qF "$bin" "$profile"; then
        return 0
    fi
    printf '\n# Taro\n%s\n' "$line" >>"$profile"
    say "added $bin to PATH in $profile"
}

check_linker() {
    if [ "$(uname -s)" = Darwin ]; then
        xcode-select -p >/dev/null 2>&1 \
            || say "note: building programs needs Apple's command line tools; run: xcode-select --install"
    elif ! command -v cc >/dev/null 2>&1; then
        say "note: building programs needs a C compiler for linking; install gcc, for example:"
        say "      sudo apt install build-essential   or   sudo dnf install gcc"
    fi
}

main() {
    need curl
    need tar
    need uname
    platform=$(detect_platform)
    tag="${TARO_VERSION:-}"
    if [ -z "$tag" ]; then
        tag=$(latest_tag) || true
        [ -n "$tag" ] || fail "could not find a Taro release; set TARO_VERSION"
    fi
    version="${tag#v}"
    name="taro-$version-$platform"
    base="${TARO_DOWNLOAD_URL:-https://github.com/$REPOSITORY/releases/download/$tag}"
    root="${TARO_INSTALL:-$HOME/.taro}"

    work=$(mktemp -d "${TMPDIR:-/tmp}/taro-install.XXXXXX")
    trap 'rm -rf "$work"' EXIT INT TERM

    say "downloading $name"
    curl -fsSL "$base/$name.tar.gz" -o "$work/$name.tar.gz" || fail "download failed: $base/$name.tar.gz"
    curl -fsSL "$base/$name.tar.gz.sha256" -o "$work/$name.tar.gz.sha256" || fail "checksum download failed"
    expected=$(cut -d ' ' -f 1 "$work/$name.tar.gz.sha256")
    actual=$(sha256 "$work/$name.tar.gz")
    [ "$expected" = "$actual" ] || fail "checksum mismatch for $name.tar.gz"

    mkdir -p "$work/unpack" "$root/toolchains"
    tar -xzf "$work/$name.tar.gz" -C "$work/unpack"
    [ -x "$work/unpack/$name/bin/taro" ] || fail "archive does not contain $name/bin/taro"
    rm -rf "$root/toolchains/$name"
    mv "$work/unpack/$name" "$root/toolchains/$name"
    ln -sfn "toolchains/$name" "$root/current"
    # Keep only the toolchain that `current` now selects.
    for toolchain in "$root"/toolchains/*; do
        [ "$toolchain" = "$root/toolchains/$name" ] || rm -rf "$toolchain"
    done

    "$root/current/bin/taro" --version >/dev/null || fail "installed taro does not run on this machine"
    say "installed $("$root/current/bin/taro" --version) to $root/toolchains/$name"

    bin="$root/current/bin"
    case ":$PATH:" in
        *":$bin:"*) ;;
        *)
            if add_to_path "$bin"; then
                say "restart your shell, or run: export PATH=\"$bin:\$PATH\""
            else
                say "add $bin to your PATH to use taro"
            fi
            ;;
    esac
    check_linker
    say "get started: taro new github.com/you/hello && cd hello && taro run"
}

main "$@"
