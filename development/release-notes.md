Preview build of the Taro SDK for macOS (Apple Silicon, macOS 14 or newer) and
Linux (x86-64 and ARM64, glibc 2.28 or newer: Ubuntu 20.04+, Debian 11+,
RHEL/AlmaLinux 8+, Fedora and similar).

## Install

```sh
curl -fsSL https://github.com/Mantton/Taro/releases/download/TAG/install.sh | TARO_VERSION=TAG sh
```

Or download the archive for your platform, check it against `SHA256SUMS`,
unpack it anywhere and add its `bin/` directory to `PATH`.

Building programs needs the system linker: Apple's command line tools on macOS
(`xcode-select --install`), or a C compiler on Linux (`build-essential` or
`gcc`).

Taro is experimental; syntax, standard-library APIs and package tooling may
change between releases.
