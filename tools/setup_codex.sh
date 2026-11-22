#!/usr/bin/env bash
# Core Codex build environment for the saved Debian 13 x86_64 image.
# No sudo, git hooks, secrets, shell startup files, or network settings changed.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
root="$PWD"
state="$root/build/codex"
mode="${1:---run}"
case "$mode" in
--run | --doctor | --dry-run) ;;
*)
  echo "Usage: bash tools/setup_codex.sh [--run|--doctor|--dry-run]" >&2
  exit 2
  ;;
esac
if [[ "$mode" == --dry-run ]]; then
  echo "Install locked Debian support packages under build/codex/system."
  echo "Install mise 2026.10.19, repository-pinned GHC/Cabal/po4a and viewer npm tools."
  echo "Install the Lean version in lean-toolchain, using the upstream release."
  echo "Use system Pandoc/LuaLaTeX and image Python >=3.12 / Node >=24."
  echo "Write build/codex.mk and build/codex/env.sh; update Cabal's HTTPS index."
  exit 0
fi
if [[ "$mode" == --doctor ]]; then
  [[ -f "$state/env.sh" ]] || {
    echo "Run bash tools/setup_codex.sh first." >&2
    exit 1
  }
  # shellcheck disable=SC1091
  source "$state/env.sh"
  "$MISE_BIN" exec -- ghc --version
  "$MISE_BIN" exec -- cabal --version
  python3 -c 'import sys; assert sys.version_info >= (3, 12)'
  node -e 'if (Number(process.versions.node.split(".")[0]) < 24) process.exit(1)'
  pandoc --version | head -1
  lualatex --version | head -1
  for tool in texfot luaotfload-tool makeindex upmendex; do command -v "$tool"; done
  for file in luatexja.sty luaotfload.sty selnolig.sty HaranoAjiMincho-Regular.otf; do kpsewhich "$file"; done
  po4a_dir="$("$MISE_BIN" where http:po4a)"
  PERL5LIB="$po4a_dir/lib:$PERL5LIB" "$po4a_dir/po4a" --version
  lean --version
  lake --version
  "$MISE_BIN" exec -- tsc --version
  "$MISE_BIN" exec -- esbuild --version
  echo "Codex core toolchain checks passed. Run the builds/tests in README.md to validate the checkout."
  exit 0
fi

python3 -c 'import sys; assert sys.version_info >= (3, 12), "Python >=3.12 required"'
node -e 'if (Number(process.versions.node.split(".")[0]) < 24) throw Error("Node >=24 required")'
for tool in pandoc lualatex kpsewhich makeindex upmendex curl git make gcc perl tar zstd dpkg-deb; do
  command -v "$tool" >/dev/null || {
    echo "Missing image prerequisite: $tool" >&2
    exit 1
  }
done
python3 tools/install_codex_debian.py
mkdir -p "$state/state" "$state/downloads" "$state/state/cabal"

# Make and interactive shells share this configuration. All mutable caches live
# in the writable checkout; plain make works in a fresh, non-activated shell.
python3 - <<'PY'
from pathlib import Path
import shlex
root = Path.cwd()
if any(c in str(root) for c in ' \t\n#$'):
    raise SystemExit("Codex checkout path must not contain whitespace, #, or $.")
p = root / 'build/codex'
prefix = p / 'system'
values = {
    'MISE_ENV': 'codex', 'MISE_DATA_DIR': str(p/'state/mise'),
    'MISE_CACHE_DIR': str(p/'state/cache'), 'MISE_CONFIG_DIR': str(p/'state/config'),
    'XDG_STATE_HOME': str(p/'state'), 'XDG_CACHE_HOME': str(p/'state/cache'),
    'ELAN_HOME': str(p/'state/elan'), 'CABAL_DIR': str(p/'state/cabal'),
    'npm_config_cache': str(p/'state/npm'),
    'TEXMFHOME': f"{prefix}/usr/share/texmf:{prefix}/usr/share/texlive/texmf-dist",
    'TEXMFVAR': str(root/'build/texmf-var'), 'TEXMFCONFIG': str(root/'build/texmf-config'),
    'PERL5LIB': f"{prefix}/usr/share/perl5:{prefix}/usr/lib/x86_64-linux-gnu/perl5/5.40",
    'LD_LIBRARY_PATH': f"{prefix}/usr/lib/x86_64-linux-gnu",
    'MISE_BIN': str(p/'mise/bin/mise'),
}
path_prefix = f"{p}/mise/bin:{p}/state/elan/bin:{prefix}/usr/bin"
shell = ''.join(f'export {k}={shlex.quote(v)}\n' for k,v in values.items())
shell += f'export PATH={shlex.quote(path_prefix)}:"$PATH"\n'
(p/'env.sh').write_text(shell)
# Make's $(shell ...) runs before exported Make variables reach recipe shells.
# Bootstrap mise's own directories there, but preserve recipe-specific values
# such as PO4A_ENV's PERL5LIB instead of sourcing the entire environment again.
mise_vars = {k:v for k,v in values.items()
             if k.startswith('MISE_') or k in ('XDG_STATE_HOME', 'ELAN_HOME')}
(p/'mise-run').write_text('#!/usr/bin/env bash\nset -euo pipefail\n' +
                         ''.join(f'export {k}={shlex.quote(v)}\n' for k,v in mise_vars.items()) +
                         'exec "$MISE_BIN" "$@"\n')
(p/'mise-run').chmod(0o755)
mk = ''.join(f'export {k} := {v}\n' for k,v in values.items())
mk += f'export PATH := {path_prefix}:$(PATH)\n'
mk += f'MISE := {p}/mise-run\nTEX_PROVIDER := system\n'
mk += f'TEXFOT := {prefix}/usr/bin/texfot\nCODEX_SETUP := 1\n'
(root/'build/codex.mk').write_text(mk)
PY
# shellcheck disable=SC1091
source "$state/env.sh"

download() {
  local url="$1" destination="$2"
  if [[ ! -f "$destination" ]]; then
    curl -fsSL --retry 3 --max-time 600 "$url" -o "$destination.tmp"
    mv "$destination.tmp" "$destination"
  fi
}
if [[ ! -x "$MISE_BIN" ]] || [[ "$("$MISE_BIN" --version | awk '{print $1}')" != "2026.10.19" ]]; then
  download https://github.com/jdx/mise/releases/download/v2026.10.19/mise-v2026.10.19-linux-x64.tar.gz "$state/downloads/mise-2026.10.19.tar.gz"
  # Update the release URL, version check, and independently recorded digest together.
  expected="b7ad610a39474b36663a6b1134c17086fa77e0f39b7ecce85c684165eed5f086"
  echo "$expected  $state/downloads/mise-2026.10.19.tar.gz" | sha256sum --check
  tar -xzf "$state/downloads/mise-2026.10.19.tar.gz" -C "$state"
fi
"$MISE_BIN" trust
"$MISE_BIN" plugin install --yes ghc https://github.com/mise-plugins/mise-ghcup
"$MISE_BIN" plugin install --yes cabal https://github.com/mise-plugins/mise-ghcup
# Pin the installer as well as the versions it installs.
for tool in ghc cabal; do
  if ! git -C "$MISE_DATA_DIR/plugins/$tool" cat-file -e 'a6407a216adc1fc08613c117c45e5c3e900da2c8^{commit}'; then
    git -C "$MISE_DATA_DIR/plugins/$tool" fetch --depth 1 origin a6407a216adc1fc08613c117c45e5c3e900da2c8
  fi
  git -C "$MISE_DATA_DIR/plugins/$tool" checkout --quiet a6407a216adc1fc08613c117c45e5c3e900da2c8
done
"$MISE_BIN" install ghc cabal http:po4a conda:gettext-tools npm:typescript npm:esbuild npm:prettier

if [[ ! -x "$ELAN_HOME/bin/elan" ]] || [[ "$("$ELAN_HOME/bin/elan" --version | awk '{print $2}')" != "4.2.4" ]]; then
  download https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz "$state/downloads/elan-4.2.4.tar.gz"
  echo "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  $state/downloads/elan-4.2.4.tar.gz" | sha256sum --check
  mkdir -p "$state/elan-installer"
  tar -xzf "$state/downloads/elan-4.2.4.tar.gz" -C "$state/elan-installer"
  "$state/elan-installer/elan-init" -y --no-modify-path --default-toolchain none
fi
toolchain="$(tr -d '[:space:]' <lean-toolchain)"
if ! "$ELAN_HOME/bin/elan" run "$toolchain" lean --version; then
  # Direct official GitHub asset avoids releases.lean-lang.org redirects, which
  # this saved environment cannot reach. Fail closed when the pin changes until
  # its release checksum is reviewed alongside this script.
  [[ "$toolchain" == leanprover/lean4:v4.35.0 ]] || {
    echo "Update the direct Lean URL/checksum for $toolchain in tools/setup_codex.sh." >&2
    exit 1
  }
  download https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst "$state/downloads/lean-4.35.0.tar.zst"
  echo "7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d  $state/downloads/lean-4.35.0.tar.zst" | sha256sum --check
  tar --zstd -xf "$state/downloads/lean-4.35.0.tar.zst" -C "$state/state"
  "$ELAN_HOME/bin/elan" toolchain link "$toolchain" "$state/state/lean-4.35.0-linux"
fi
if [[ ! -f "$CABAL_DIR/config" ]]; then
  "$MISE_BIN" exec -- cabal user-config init
  # Cabal's default URL is HTTP. Use the official HTTPS endpoint with secure
  # repository verification left enabled.
  sed -i 's|url: http://hackage.haskell.org/|url: https://hackage.haskell.org/|' "$CABAL_DIR/config"
fi
"$MISE_BIN" exec -- cabal update
luaotfload-tool --update
bash tools/setup_codex.sh --doctor
