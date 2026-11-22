#!/usr/bin/env bash
#
# Provisions the build toolchain. Dry-run by default; pass --run to install.
#
# What it does, in short:
#   - mise is the version manager for everything except TeX. On macOS it is
#     installed via Homebrew when missing; on Linux the system package manager
#     (apt-get, dnf, paru, pacman, then Homebrew) is used only for build basics
#     like curl/git/make, and mise itself is installed when needed.
#   - mise then installs the pinned GHC, cabal, Python, Pandoc (from mise.toml)
#     plus the Node/TypeScript/esbuild/tree-sitter/elan tooling. GHC and cabal
#     use the ghcup backend (registered below), not mise's default conda backend,
#     which lacks the pinned GHC on some platforms.
#   - TeX is a repo-local TeX Live tree under .texlive/, with packages pulled by
#     tlmgr from a frozen, dated tlnet snapshot for reproducibility (override via
#     TLMGR_REPOSITORY). The Makefile calls those binaries by absolute path, so
#     the build never falls back to a system TeX.
#   - The pinned Lean toolchain (lean-toolchain) is provisioned for the
#     formalization viewer/LSP tooling only, not the PDF book build; skip it with
#     PROVISION_LEAN=0.
#   - po4a and GNU gettext maintain localized chapter catalogs and regenerate
#     translated Markdown. po4a is a mise-managed tool (http:po4a in mise.toml);
#     its two CPAN Perl dependencies are built against the system Perl into the
#     repo-local .perllib/. GNU gettext is pinned in mise.toml (conda:gettext-tools).
#
# `make` runs every tool through mise except TeX, so mise must be on PATH; if it
# is reported missing, re-run ./setup.sh --run and restart your shell, or pass
# MISE=/path/to/mise. See README.md ("Setup") for the full rationale.

set -euo pipefail

DRY_RUN=1
DOCTOR=0
MISE_BIN="${MISE_BIN:-}"
BREW_BIN="${BREW_BIN:-}"

# Reproducible TeX Live package source. The default is a frozen, dated tlnet
# snapshot from the TeX Live archive (2026/10/25 -> TeX Live 2026). The
# repo-local TeX Live tree under .texlive/ is built and its packages installed
# from this snapshot, so repeated installs and updates use the same packages.
# Override with another archive date, a local mirror, or the keyword `ctan` for
# the live default; bump the date deliberately.
TLMGR_REPOSITORY="${TLMGR_REPOSITORY:-https://www.texlive.info/tlnet-archive/2026/10/25/tlnet}"
TEXLIVE_ROOT="${TEXLIVE_ROOT:-${PWD}/.texlive}"
TEXLIVE_INSTALL_ROOT="${TEXLIVE_INSTALL_ROOT:-${TEXLIVE_ROOT}/texlive}"

# The pinned Lean toolchain (lean-toolchain + elan in mise.toml) is needed by the
# formalization viewer/LSP tooling, not by the PDF book build. Set to 0 to skip
# provisioning the Lean compiler during setup.
PROVISION_LEAN="${PROVISION_LEAN:-1}"

TEXLIVE_PACKAGES=(
  amscls
  amsfonts
  amsmath
  bookmark
  booktabs
  caption
  etoolbox
  fancyhdr
  fontspec
  footnotehyper
  geometry
  haranoaji
  hyperref
  latex
  latex-bin
  lm
  latexdiff
  luatex
  luatexja
  luaotfload
  lualatex-math
  makeindex
  microtype
  parskip
  pgf
  regexpatch
  selnolig
  texfot
  tools
  unicode-math
  upmendex
  upquote
  ulem
  xcolor
  xkeyval
  xurl
)

# po4a itself is pinned and provisioned by mise (see the http:po4a tool in
# mise.toml); this minimum only guards against a resolved po4a that is somehow
# older than what the translation workflow needs. The Makefile and po4a.cfg use
# options (e.g. --wrap-po, --width) and rely on PO/POT output formatting that
# older builds such as Ubuntu noble's 0.69 do not reproduce.
PO4A_MIN_VERSION="0.74"

# po4a is a Perl app whose two non-core CPAN dependencies mise does not manage.
# They are installed against the system Perl into a repo-local library tree
# (analogous to .texlive/) so no sudo or distribution Perl packages are needed;
# the Makefile puts this on PERL5LIB when it runs po4a. YAML::Tiny is pure Perl;
# Syntax::Keyword::Try is XS, so a C compiler and make (part of the build basics
# below) are required to build it.
PERL_MODULES=(YAML::Tiny Syntax::Keyword::Try)
PERL_LOCAL_LIB="${PERL_LOCAL_LIB:-${PWD}/.perllib}"
CPANM_URL="${CPANM_URL:-https://cpanmin.us}"

GETTEXT_COMMANDS=(
  msgattrib
  msgcat
  msgcmp
  msgfmt
  msggrep
  msginit
  msgmerge
)

log() {
  echo "$@" >&2
}

usage() {
  cat >&2 <<'EOF'
Usage: ./setup.sh [--dry-run|--run|--doctor]

Options:
  --dry-run  Print commands without running them. This is the default.
  --run      Install packages and update toolchains.
  --doctor   Check that the setup is already usable without installing anything.
  -h, --help Show this help.
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
  --dry-run)
    DRY_RUN=1
    ;;
  --run | --apply)
    DRY_RUN=0
    ;;
  --doctor)
    DRY_RUN=0
    DOCTOR=1
    ;;
  -h | --help)
    usage
    exit 0
    ;;
  *)
    log "❌ Unknown option: $1"
    usage
    exit 1
    ;;
  esac
  shift
done

format_cmd() {
  printf '%q ' "$@"
}

run_cmd() {
  log "+ $(format_cmd "$@")"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    return
  fi
  "$@"
}

find_cmd() {
  local name="$1"
  shift

  if command -v "${name}" >/dev/null 2>&1; then
    command -v "${name}"
    return 0
  fi

  local candidate
  for candidate in "$@"; do
    if [[ -x "${candidate}" ]]; then
      printf '%s\n' "${candidate}"
      return 0
    fi
  done

  return 1
}

find_mise() {
  # Match Makefile: prefer a direct executable over a mise-managed mise shim.
  local on_path candidate
  on_path="$(command -v mise 2>/dev/null || true)"
  if [[ -n "${on_path}" && "${on_path}" != */shims/mise ]]; then
    printf '%s\n' "${on_path}"
    return 0
  fi
  for candidate in \
    /opt/homebrew/bin/mise \
    /usr/local/bin/mise \
    /home/linuxbrew/.linuxbrew/bin/mise \
    "${HOME}/.local/bin/mise" \
    "${HOME}/.cargo/bin/mise"; do
    if [[ -x "${candidate}" ]]; then
      printf '%s\n' "${candidate}"
      return 0
    fi
  done
  if [[ -n "${on_path}" ]]; then
    printf '%s\n' "${on_path}"
    return 0
  fi
  return 1
}

find_brew() {
  find_cmd brew \
    /opt/homebrew/bin/brew \
    /usr/local/bin/brew \
    /home/linuxbrew/.linuxbrew/bin/brew
}

set_mise_bin() {
  if [[ -n "${MISE_BIN}" && -x "${MISE_BIN}" ]]; then
    return
  fi

  if MISE_BIN="$(find_mise)"; then
    export MISE_BIN
    return
  fi

  MISE_BIN=""
}

set_brew_bin() {
  if [[ -n "${BREW_BIN}" && -x "${BREW_BIN}" ]]; then
    return
  fi

  if BREW_BIN="$(find_brew)"; then
    export BREW_BIN
    return
  fi

  BREW_BIN=""
}

# GNU gettext is pinned in mise.toml (conda:gettext-tools); put its bin dir on PATH
# so the gettext checks and po4a find it. A no-op before `mise install`.
ensure_gettext_on_path() {
  local mise home
  mise="$(mise_cmd)" || return 0
  home="$("${mise}" where "conda:gettext-tools" 2>/dev/null)" || return 0
  [[ -n "${home}" && -d "${home}/bin" ]] || return 0
  case ":${PATH}:" in
  *":${home}/bin:"*) ;;
  *)
    PATH="${home}/bin:${PATH}"
    export PATH
    ;;
  esac
}

# PERL5LIB for running the mise-managed po4a: the repo-local CPAN tree first,
# then the po4a install's bundled Locale::Po4a modules, then any inherited path.
# Mirrors the Makefile's PO4A_PERL5LIB.
po4a_perl5lib() {
  local home="$1"
  printf '%s' "${PERL_LOCAL_LIB}/lib/perl5:${home}/lib${PERL5LIB:+:${PERL5LIB}}"
}

# Absolute path to the po4a script provisioned by mise's http backend, or a
# non-zero exit when it is not installed yet.
po4a_bin_path() {
  local mise home
  mise="$(mise_cmd)" || return 1
  home="$("${mise}" where "http:po4a" 2>/dev/null)" || return 1
  [[ -n "${home}" && -x "${home}/po4a" ]] || return 1
  printf '%s' "${home}/po4a"
}

po4a_version_available() {
  local po4a home
  po4a="$(po4a_bin_path)" || return 1
  home="$(dirname "${po4a}")"
  PERL5LIB="$(po4a_perl5lib "${home}")" "${po4a}" --version
}

# True when a Perl module loads under the system Perl with the repo-local CPAN
# tree prepended to @INC.
perl_module_present() {
  PERL5LIB="${PERL_LOCAL_LIB}/lib/perl5${PERL5LIB:+:${PERL5LIB}}" \
    perl -M"$1" -e1 >/dev/null 2>&1
}

perl_modules_available() {
  command -v perl >/dev/null 2>&1 || return 1
  local module
  for module in "${PERL_MODULES[@]}"; do
    perl_module_present "${module}" || return 1
  done
}

gettext_version_available() {
  local command
  if ! command="$(find_cmd "$1")"; then
    return 1
  fi
  "${command}" --version
}

# Compare dotted numeric versions ("$1" >= "$2") without `sort -V`, which the
# BSD sort on some macOS releases does not support.
version_ge() {
  local -a lhs rhs
  local IFS=.
  read -r -a lhs <<<"$1"
  read -r -a rhs <<<"$2"
  local i max="${#lhs[@]}"
  ((${#rhs[@]} > max)) && max="${#rhs[@]}"
  for ((i = 0; i < max; i++)); do
    local l=$((10#${lhs[i]:-0})) r=$((10#${rhs[i]:-0}))
    ((l > r)) && return 0
    ((l < r)) && return 1
  done
  return 0
}

po4a_version_ok() {
  local version
  version="$(po4a_version_available 2>/dev/null | sed -n 's/^po4a version \([0-9][0-9.]*\).*$/\1/p')"
  [[ -n "${version}" ]] || return 1
  version_ge "${version}" "${PO4A_MIN_VERSION}"
}

mise_cmd() {
  if [[ -z "${MISE_BIN}" ]]; then
    set_mise_bin
  fi

  if [[ -z "${MISE_BIN}" ]]; then
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      printf 'mise'
      return
    fi
    log "❌ Required command not found: mise"
    exit 1
  fi

  printf '%s' "${MISE_BIN}"
}

run_mise() {
  local mise
  mise="$(mise_cmd)"
  run_cmd "${mise}" "$@"
}

elan_bin() {
  # elan is resolved only from the project-controlled location. The pinned mise
  # github:leanprover/elan tool provides elan-init (see elan_init_bin), which
  # installs elan into ~/.elan; mise.toml puts ~/.elan/bin on PATH. We do not
  # fall back to a bare `command -v elan`, so an unpinned system elan elsewhere
  # on PATH is never used: `make doctor` then reports Lean tooling as
  # unavailable rather than silently accepting an off-version elan.
  if [[ -x "${HOME}/.elan/bin/elan" ]]; then
    printf '%s\n' "${HOME}/.elan/bin/elan"
    return 0
  fi

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    printf '%s\n' "${HOME}/.elan/bin/elan"
    return 0
  fi

  return 1
}

elan_init_bin() {
  local mise prefix
  mise="$(mise_cmd)"
  if prefix="$("${mise}" where github:leanprover/elan 2>/dev/null)" && [[ -x "${prefix}/elan-init" ]]; then
    printf '%s\n' "${prefix}/elan-init"
    return 0
  fi
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    printf '%s\n' "${HOME}/.local/share/mise/installs/github-leanprover-elan/<version>/elan-init"
    return 0
  fi
  return 1
}

ensure_elan() {
  local init installed expected current
  if ! init="$(elan_init_bin)"; then
    return 1
  fi
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    run_cmd "${init}" -y --no-modify-path --default-toolchain none
    return 0
  fi
  expected="$("${init}" --version | awk '{print $2}')" || return 1
  [[ -n "${expected}" ]] || return 1
  if installed="$(elan_bin)" && current="$("${installed}" --version | awk '{print $2}')" && [[ "${current}" == "${expected}" ]]; then
    return 0
  fi
  if ! run_cmd "${init}" -y --no-modify-path --default-toolchain none; then
    return 1
  fi
  installed="$(elan_bin)" || return 1
  [[ "$("${installed}" --version | awk '{print $2}')" == "${expected}" ]]
}

RESOLVED_TEX_CMD=()

# TeX Live's name for this host's binary directory, or empty when unknown.
texlive_host_platform() {
  case "$(uname -s)-$(uname -m)" in
  Darwin-*) echo universal-darwin ;;
  Linux-aarch64 | Linux-arm64) echo aarch64-linux ;;
  Linux-x86_64) echo x86_64-linux ;;
  esac
}

# The tree may hold binaries for several platforms (a checkout shared between
# macOS and a Linux VM), so only the host's bin dir counts; on hosts without a
# known platform name, fall back to every bin dir.
texlive_bin_dirs() {
  local platform
  platform="$(texlive_host_platform)"
  if [[ -n "${platform}" ]]; then
    if [[ -d "${TEXLIVE_INSTALL_ROOT}/bin/${platform}" ]]; then
      printf '%s\n' "${TEXLIVE_INSTALL_ROOT}/bin/${platform}"
    fi
  elif [[ -d "${TEXLIVE_INSTALL_ROOT}/bin" ]]; then
    find "${TEXLIVE_INSTALL_ROOT}/bin" -mindepth 1 -maxdepth 1 -type d 2>/dev/null | sort
  fi
}

texlive_repository_url() {
  if [[ "${TLMGR_REPOSITORY}" == "ctan" ]]; then
    printf '%s\n' "https://mirror.ctan.org/systems/texlive/tlnet"
  else
    printf '%s\n' "${TLMGR_REPOSITORY%/}"
  fi
}

# A tree installed on another platform has every package but no binaries for
# this host. Bootstrap this platform's kpathsea and tlmgr from the pinned
# repository, then let `tlmgr platform add` fetch the remaining binaries,
# instead of deleting a tree the other platform still uses.
# TAR_OPTIONS=--absolute-names makes GNU tar create ../ symlinks directly; its
# default placeholder files cannot be replaced on some shared VM folders.
add_texlive_host_platform() {
  local platform archive pkg
  platform="$(texlive_host_platform)"
  [[ -n "${platform}" && -f "${TEXLIVE_INSTALL_ROOT}/tlpkg/texlive.tlpdb" ]] || return 0
  [[ -d "${TEXLIVE_INSTALL_ROOT}/bin/${platform}" ]] && return 0
  log "--- 🇯🇵 Adding ${platform} binaries to the repo-local TeX Live tree ---"
  archive="$(texlive_repository_url)/archive"
  for pkg in kpathsea texlive.infra; do
    log "+ curl -fsSL ${archive}/${pkg}.${platform}.tar.xz | tar -xJ -C ${TEXLIVE_INSTALL_ROOT}"
    if [[ "${DRY_RUN}" -eq 0 ]]; then
      curl -fsSL "${archive}/${pkg}.${platform}.tar.xz" |
        TAR_OPTIONS=--absolute-names tar -xJ -C "${TEXLIVE_INSTALL_ROOT}"
    fi
  done
  TAR_OPTIONS=--absolute-names run_cmd "${TEXLIVE_INSTALL_ROOT}/bin/${platform}/tlmgr" platform add "${platform}"
}

# Prepend the repo-local TeX Live bin dir to PATH once, so TeX tools resolve
# their sibling binaries (kpsewhich, mktexfmt, ...) without every invocation
# repeating a long `env PATH=<texbin>:$PATH` prefix. Mirrors how the mise bin
# dir is put on PATH below. Idempotent and logged once; a no-op before the
# snapshot exists (e.g. dry-run), where commands are only printed anyway.
texlive_path_ready=0
ensure_texlive_on_path() {
  [[ "${texlive_path_ready}" -eq 1 ]] && return 0
  local tex_bin_dir
  tex_bin_dir="$(texlive_bin_dirs | head -n 1)"
  [[ -z "${tex_bin_dir}" ]] && return 0
  case ":${PATH}:" in
  *":${tex_bin_dir}:"*) ;;
  *)
    PATH="${tex_bin_dir}:${PATH}"
    export PATH
    log "+ export PATH=${tex_bin_dir}:\$PATH   # repo-local TeX Live on PATH (set once)"
    ;;
  esac
  texlive_path_ready=1
}

resolve_tex_cmd() {
  local name="$1"
  RESOLVED_TEX_CMD=()

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    RESOLVED_TEX_CMD=("${TEXLIVE_INSTALL_ROOT}/bin/<platform>/${name}")
    return 0
  fi

  # TeX comes only from the repo-local TeX Live snapshot under .texlive/. We
  # never fall back to a system TeX, so `make doctor` fails loudly when the
  # snapshot is missing rather than silently using an unpinned TeX.
  local tex_bin_dir
  while IFS= read -r tex_bin_dir; do
    if [[ -x "${tex_bin_dir}/${name}" ]]; then
      RESOLVED_TEX_CMD=("${tex_bin_dir}/${name}")
      return 0
    fi
  done < <(texlive_bin_dirs)

  return 1
}

run_tex_cmd() {
  local name="$1"
  shift

  if ! resolve_tex_cmd "${name}"; then
    log "❌ Required TeX command not found: ${name}"
    log "   The repo-local TeX Live snapshot under .texlive/ does not provide"
    log "   '${name}'. Only this project-controlled TeX is used; a system TeX"
    log "   is never picked up. Rerun './setup.sh --run' to build the snapshot."
    exit 1
  fi

  ensure_texlive_on_path
  run_cmd "${RESOLVED_TEX_CMD[@]}" "$@"
}

check_tex_cmd_available() {
  local name="$1"
  if ! resolve_tex_cmd "${name}"; then
    log "❌ Required TeX command not found: ${name}"
    exit 1
  fi
  log "+ $(format_cmd "${RESOLVED_TEX_CMD[@]}")"
}

texlive_install_url() {
  if [[ "${TLMGR_REPOSITORY}" == "ctan" ]]; then
    printf '%s\n' "https://mirror.ctan.org/systems/texlive/tlnet/install-tl-unx.tar.gz"
  else
    printf '%s\n' "${TLMGR_REPOSITORY%/}/install-tl-unx.tar.gz"
  fi
}

repo_texlive_complete() {
  local has_lualatex=0
  local has_luaotfload=0
  local tex_bin_dir
  while IFS= read -r tex_bin_dir; do
    [[ -x "${tex_bin_dir}/lualatex" ]] && has_lualatex=1
    [[ -x "${tex_bin_dir}/luaotfload-tool" ]] && has_luaotfload=1
  done < <(texlive_bin_dirs)
  [[ "${has_lualatex}" -eq 1 && "${has_luaotfload}" -eq 1 ]]
}

install_repo_texlive() {
  add_texlive_host_platform
  if resolve_tex_cmd tlmgr && [[ "${RESOLVED_TEX_CMD[0]}" == "${TEXLIVE_ROOT}"/* ]] && repo_texlive_complete; then
    log "--- 🇯🇵 Repo-local TeX Live already installed at ${TEXLIVE_ROOT} ---"
    return
  fi

  log "--- 🇯🇵 Installing repo-local TeX Live at ${TEXLIVE_INSTALL_ROOT} ---"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    run_cmd mkdir -p "${TEXLIVE_INSTALL_ROOT}"
    run_cmd curl -fsSL "$(texlive_install_url)" -o "<temporary install-tl archive>"
    run_cmd install-tl -profile "<generated profile>"
    return
  fi

  require_cmd curl
  require_cmd tar

  if [[ -d "${TEXLIVE_INSTALL_ROOT}" ]] && ! repo_texlive_complete; then
    log "Removing incomplete repo-local TeX Live tree: ${TEXLIVE_INSTALL_ROOT}"
    bash tools/remove_setup_cache.sh "${PWD}" "${TEXLIVE_INSTALL_ROOT}"
  fi

  local tmpdir archive installer profile
  tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/texlive-install.XXXXXX")"
  archive="${tmpdir}/install-tl-unx.tar.gz"
  profile="${tmpdir}/texlive.profile"

  if ! curl -fsSL "$(texlive_install_url)" -o "${archive}"; then
    rm -rf "${tmpdir}"
    log "❌ Failed to download TeX Live installer from $(texlive_install_url)"
    exit 1
  fi
  # Lock the executable installer as well as the dated package repository.
  # Update the default URL and this digest together. Custom mirrors may supply
  # TEXLIVE_INSTALL_SHA256; their HTTPS endpoint is otherwise the trust boundary.
  local expected_sha actual_sha
  expected_sha="${TEXLIVE_INSTALL_SHA256:-}"
  if [[ -z "${expected_sha}" && "$(texlive_repository_url)" == "https://www.texlive.info/tlnet-archive/2026/10/25/tlnet" ]]; then
    expected_sha="df872fe2aa1278af8199edcab7deb7f3a045e776afeb511bf9a317be64bdb7f7"
  fi
  if [[ -n "${expected_sha}" ]]; then
    if command -v sha256sum >/dev/null 2>&1; then
      actual_sha="$(sha256sum "${archive}")"
    else
      require_cmd shasum
      actual_sha="$(shasum -a 256 "${archive}")"
    fi
    if [[ "${actual_sha%% *}" != "${expected_sha}" ]]; then
      rm -rf "${tmpdir}"
      log "❌ TeX Live installer SHA256 mismatch; refusing to execute it."
      exit 1
    fi
  else
    log "Custom TeX Live repository: set TEXLIVE_INSTALL_SHA256 to pin its installer."
  fi
  if ! tar -xzf "${archive}" -C "${tmpdir}"; then
    rm -rf "${tmpdir}"
    log "❌ Failed to unpack TeX Live installer"
    exit 1
  fi
  installer="$(find "${tmpdir}" -maxdepth 2 -type f -name install-tl | sort | head -n 1)"
  if [[ -z "${installer}" ]]; then
    rm -rf "${tmpdir}"
    log "❌ Could not find install-tl in downloaded TeX Live installer."
    exit 1
  fi

  mkdir -p "${TEXLIVE_INSTALL_ROOT}"
  cat >"${profile}" <<EOF
selected_scheme scheme-infraonly
TEXDIR ${TEXLIVE_INSTALL_ROOT}
TEXMFLOCAL ${TEXLIVE_ROOT}/texmf-local
TEXMFSYSVAR ${TEXLIVE_ROOT}/texmf-var
TEXMFSYSCONFIG ${TEXLIVE_ROOT}/texmf-config
TEXMFCONFIG ${TEXLIVE_ROOT}/texmf-config
TEXMFVAR ${TEXLIVE_ROOT}/texmf-var
TEXMFHOME ${TEXLIVE_ROOT}/texmf-home
option_doc 0
option_src 0
tlpdbopt_install_docfiles 0
tlpdbopt_install_srcfiles 0
EOF

  "${installer}" -profile "${profile}" -repository "$(texlive_repository_url)"
  rm -rf "${tmpdir}"
}

doctor_failed=0

doctor_ok() {
  log "✅ $1"
}

doctor_fail() {
  log "❌ $1"
  doctor_failed=1
}

doctor_check() {
  local description="$1"
  shift

  if "$@" >/dev/null 2>&1; then
    doctor_ok "${description}"
  else
    doctor_fail "${description}"
  fi
}

doctor_mise_check() {
  local description="$1"
  shift
  local tool="$1"

  # `mise exec -- TOOL` passes the ambient PATH through, so it silently runs a
  # system TOOL when the pinned one is missing or broken (for example
  # `mise exec -- git` resolves to /usr/bin/git). `mise which TOOL` instead
  # resolves only a mise-managed install and exits non-zero otherwise, so gate
  # on it before confirming the tool runs: a system fallthrough then fails the
  # check instead of masquerading as a healthy pinned tool.
  local mise
  mise="$(mise_cmd)"
  if "${mise}" which "${tool}" >/dev/null 2>&1 && "${mise}" exec -- "$@" >/dev/null 2>&1; then
    doctor_ok "${description}"
  else
    doctor_fail "${description}"
    mise_doctor_hint "${tool}"
  fi
}

mise_doctor_hint_shown=0
mise_doctor_hint() {
  [[ "${mise_doctor_hint_shown}" -eq 1 ]] && return
  mise_doctor_hint_shown=1
  log "   ↳ '$1' is not provided by the pinned mise toolchain (it is missing,"
  log "     broken, or only present as an unpinned system tool). Build tools"
  log "     come only from mise; system versions are never used. Run"
  log "     './setup.sh --run' to install the pinned tools, then retry 'make doctor'."
}

doctor_elan_check() {
  local elan
  if elan="$(elan_bin)" && "${elan}" --version >/dev/null 2>&1; then
    doctor_ok "elan available"
  else
    log "⚠️  elan available — optional, needed only for Lean tooling; run './setup.sh --run'."
  fi
}

tex_doctor_hint_shown=0
tex_doctor_hint() {
  [[ "${tex_doctor_hint_shown}" -eq 1 ]] && return
  tex_doctor_hint_shown=1
  log "   ↳ TeX comes only from the repo-local TeX Live snapshot under .texlive/,"
  log "     never a system TeX. The snapshot is missing or incomplete."
  log "     Run './setup.sh --run' to build it, then retry 'make doctor'."
}

doctor_tex_check() {
  local description="$1"
  local name="$2"
  shift 2

  if resolve_tex_cmd "${name}"; then
    ensure_texlive_on_path
    if "${RESOLVED_TEX_CMD[@]}" "$@" >/dev/null 2>&1; then
      doctor_ok "${description}"
      return
    fi
  fi
  doctor_fail "${description}"
  tex_doctor_hint
}

doctor_tex_available_check() {
  local description="$1"
  local name="$2"

  if resolve_tex_cmd "${name}"; then
    doctor_ok "${description}"
  else
    doctor_fail "${description}"
    tex_doctor_hint
  fi
}

doctor_lean_toolchain_check() {
  local toolchain
  toolchain="$(tr -d '[:space:]' <lean-toolchain 2>/dev/null || true)"
  if [[ -z "${toolchain}" ]]; then
    log "⚠️  lean-toolchain missing or empty; skipping Lean toolchain check."
    return
  fi
  local elan
  if ! elan="$(elan_bin)"; then
    log "⚠️  elan not installed — optional, needed only for Lean tooling; run './setup.sh --run'."
    return
  fi

  # Check `elan toolchain list` rather than invoking `lean`, because a bare
  # `lean` invocation makes elan auto-install the toolchain, which doctor must
  # not do. Capture first, then grep, to avoid a SIGPIPE-under-pipefail report.
  local toolchains
  toolchains="$("${elan}" toolchain list 2>/dev/null)" || true
  if printf '%s\n' "${toolchains}" | grep -qF "${toolchain}"; then
    doctor_ok "Lean toolchain ${toolchain} installed"
  else
    log "⚠️  Lean toolchain ${toolchain} not installed — optional, needed only for Lean tooling; run './setup.sh --run'."
  fi
}

doctor_mise_trust_check() {
  # Capture first, then grep: `... | grep -q` under `set -o pipefail` can report
  # the upstream SIGPIPE (grep exits early on first match) as a pipeline failure.
  local trust_output
  trust_output=$(run_mise trust --show 2>/dev/null) || true
  if printf '%s\n' "${trust_output}" | grep -Eq ': trusted$'; then
    doctor_ok "mise project trusted"
  else
    doctor_fail "mise project trusted"
  fi
}

doctor_lefthook_hook_check() {
  # lefthook installs a pre-commit hook that runs `make lint`. Resolve the hook
  # path through git so this still works under worktrees or a custom hooksPath.
  local hook
  hook="$(git rev-parse --git-path hooks/pre-commit 2>/dev/null || true)"
  if [[ -n "${hook}" && -f "${hook}" ]] && grep -q lefthook "${hook}" 2>/dev/null; then
    doctor_ok "git pre-commit hook installed (lefthook)"
  else
    doctor_fail "git pre-commit hook installed (lefthook)"
    log "   ↳ Run 'mise exec -- lefthook install' (or './setup.sh --run') to install git hooks."
    return
  fi
  if grep -qF "${LEFTHOOK_MISSING_LINE}" "${hook}" 2>/dev/null; then
    doctor_fail "git pre-commit hook fails when lefthook is missing"
    log "   ↳ Run './setup.sh --run' to harden the generated hook."
  else
    doctor_ok "git pre-commit hook fails when lefthook is missing"
  fi
}

# lefthook's generated hook prints "Can't find lefthook in PATH" and exits 0
# when it cannot locate the binary, so a commit from a shell without the mise
# toolchain silently skips `make lint`. Rewrite that fallback to fail instead;
# LEFTHOOK=0 remains the explicit bypass handled at the top of the hook.
# `lefthook install` regenerates the hooks, so this runs after every install.
LEFTHOOK_MISSING_LINE='echo "Can'"'"'t find lefthook in PATH"'

harden_lefthook_hooks() {
  local hooks_dir hook tmp
  hooks_dir="$(git rev-parse --git-path hooks 2>/dev/null || true)"
  [[ -n "${hooks_dir}" && -d "${hooks_dir}" ]] || return 0
  for hook in "${hooks_dir}"/*; do
    [[ -f "${hook}" && "${hook}" != *.sample ]] || continue
    grep -qF "${LEFTHOOK_MISSING_LINE}" "${hook}" || continue
    log "+ harden ${hook} (fail when lefthook is missing)"
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      continue
    fi
    tmp="${hook}.tmp.$$"
    awk -v needle="${LEFTHOOK_MISSING_LINE}" '
      {
        i = index($0, needle)
        if (i > 0) {
          indent = substr($0, 1, i - 1)
          print indent "echo \"Can'"'"'t find lefthook in PATH; refusing to skip the git hook.\" >&2"
          print indent "echo \"Run ./setup.sh --run, or set LEFTHOOK=0 to bypass deliberately.\" >&2"
          print indent "exit 1"
        } else {
          print
        }
      }
    ' "${hook}" >"${tmp}"
    chmod +x "${tmp}"
    mv "${tmp}" "${hook}"
  done
}

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      log "Dry-run: command not currently found, but would be required: $1"
      return
    fi
    log "❌ Required command not found: $1"
    exit 1
  fi
}

sudo_cmd() {
  if [[ "${EUID}" -eq 0 ]]; then
    run_cmd "$@"
  else
    if [[ "${DRY_RUN}" -eq 0 ]]; then
      require_cmd sudo
    fi
    run_cmd sudo "$@"
  fi
}

install_macos() {
  log "✅ Running on macOS"
  local command_name
  for command_name in cc make; do
    if ! command -v "${command_name}" >/dev/null 2>&1; then
      log "Missing ${command_name}: install Xcode Command Line Tools with xcode-select --install."
      [[ "${DRY_RUN}" -eq 1 ]] || exit 1
    fi
  done

  set_mise_bin
  if [[ -n "${MISE_BIN}" ]]; then
    log "--- 🛠 mise already installed at ${MISE_BIN} ---"
    return
  fi

  set_brew_bin
  if [[ -z "${BREW_BIN}" ]]; then
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      log "Dry-run: Homebrew not currently found, but would be required to install mise."
    else
      log "Homebrew not found. Install mise first, for example with Homebrew or https://mise.jdx.dev/."
      exit 1
    fi
  fi

  log "--- 📦 Installing mise via Homebrew ---"
  run_cmd "${BREW_BIN:-brew}" install mise
  set_mise_bin
}

install_mise_linux() {
  set_mise_bin
  if [[ -n "${MISE_BIN}" ]]; then
    return
  fi

  set_brew_bin
  if [[ -n "${BREW_BIN}" ]]; then
    run_cmd "${BREW_BIN}" install mise
    return
  fi

  require_cmd curl
  log "--- 🛠 Installing mise ---"
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    log "Dry-run: would download https://mise.run and run its installer."
    return
  fi
  local mise_installer
  mise_installer=$(mktemp) || exit 1
  # mise.run is a floating installer (the one unpinned executable in an
  # otherwise version-pinned toolchain). For a reproducible, auditable
  # bootstrap, export MISE_VERSION (e.g. MISE_VERSION=v2025.1.0) before running
  # this script — the installer honours it, and run_cmd inherits the env.
  if [[ -n "${MISE_VERSION:-}" ]]; then
    log "Pinning mise to ${MISE_VERSION}"
  fi
  if ! curl -fsSL https://mise.run -o "$mise_installer" || [[ ! -s "$mise_installer" ]]; then
    log "❌ Failed to download mise installer"
    rm -f "$mise_installer"
    exit 1
  fi
  if ! run_cmd sh "$mise_installer"; then
    log "❌ Failed to run mise installer"
    rm -f "$mise_installer"
    exit 1
  fi
  rm -f "$mise_installer"
  set_mise_bin
}

# Commands the Linux build needs from the system: a C compiler for GHC and the
# XS Perl module, make, and curl/git for fetching tools.
LINUX_BUILD_BASICS=(cc make curl git)

linux_build_basics_available() {
  local cmd
  for cmd in "${LINUX_BUILD_BASICS[@]}"; do
    command -v "${cmd}" >/dev/null 2>&1 || return 1
  done
}

install_linux() {
  log "✅ Running on Linux"
  local found_system_manager=0

  # Only the build basics come from the system; gettext and libgmp (for linking
  # book-filter) are pinned in mise.toml. Skip the package manager, and with it
  # sudo, when the basics are already present (e.g. a rootless VM).
  if linux_build_basics_available; then
    log "--- 📦 System build tools already installed (${LINUX_BUILD_BASICS[*]}) ---"
    found_system_manager=1
  elif command -v apt-get >/dev/null 2>&1; then
    found_system_manager=1
    log "--- 📦 Installing System Tools via apt ---"
    sudo_cmd apt-get update
    sudo_cmd apt-get install -y build-essential ca-certificates curl git make
  elif command -v dnf >/dev/null 2>&1; then
    found_system_manager=1
    log "--- 📦 Installing System Tools via dnf ---"
    sudo_cmd dnf install -y ca-certificates curl gcc gcc-c++ git make
  elif command -v paru >/dev/null 2>&1; then
    found_system_manager=1
    log "--- 📦 Installing System Tools via paru ---"
    run_cmd paru -S --needed --noconfirm base-devel ca-certificates curl git make
  elif command -v pacman >/dev/null 2>&1; then
    found_system_manager=1
    log "--- 📦 Installing System Tools via pacman ---"
    sudo_cmd pacman -S --needed --noconfirm base-devel ca-certificates curl git make
  else
    set_brew_bin
  fi

  if [[ "${found_system_manager}" -eq 0 && -z "${BREW_BIN}" ]]; then
    log "❌ Unsupported Linux distribution."
    log "Install curl, git, make, and mise, then rerun this script."
    exit 1
  fi

  install_mise_linux
}

# po4a itself is a mise-managed tool (http:po4a in mise.toml) installed by the
# later `mise install` step, as is GNU gettext (conda:gettext-tools).
# This function provisions only po4a's CPAN Perl modules.
install_translation_tools() {
  install_perl_modules
}

# Install po4a's CPAN dependencies against the system Perl into the repo-local
# ${PERL_LOCAL_LIB} (no sudo, no distribution Perl packages). Uses a system
# cpanm when present, otherwise the self-contained App::cpanminus script fetched
# over curl; both only need core Perl plus the C toolchain from the build
# basics. Like the mise.run bootstrap, the fallback cpanmin.us script is a
# floating HTTPS installer, not a checksum-locked download. Prefer a packaged
# system cpanm when bootstrap reproducibility is required. The XS module (Syntax::Keyword::Try) is compiled here.
install_perl_modules() {
  if perl_modules_available; then
    log "--- 🌐 po4a Perl modules already installed (${PERL_MODULES[*]}) ---"
    return
  fi

  if ! command -v perl >/dev/null 2>&1; then
    if [[ "${DRY_RUN}" -eq 1 ]]; then
      log "Dry-run: perl not found; it is required to build po4a's Perl modules."
      return
    fi
    log "❌ perl not found; install a system Perl (with a C compiler and make) and rerun setup."
    exit 1
  fi

  # Reaching here means some module does not load, which after a system Perl
  # upgrade is true of every compiled object in the tree: the .so files no
  # longer match the interpreter's ABI, while the .pm files still record the
  # current version. cpanm reads those versions, calls the distributions up to
  # date and skips them, and the stale objects of transitive XS dependencies
  # break the next build anyway. The tree is a derived cache, so discard it and
  # let cpanm compile everything against the Perl now installed.
  if [[ -d "${PERL_LOCAL_LIB}" ]]; then
    log "--- 🌐 Discarding the unusable Perl tree in ${PERL_LOCAL_LIB} ---"
    run_cmd bash tools/remove_setup_cache.sh "${PWD}" "${PERL_LOCAL_LIB}"
  fi

  log "--- 🌐 Installing po4a Perl modules into ${PERL_LOCAL_LIB} (${PERL_MODULES[*]}) ---"
  local cpanm
  if cpanm="$(find_cmd cpanm)"; then
    run_cmd "${cpanm}" --notest --local-lib "${PERL_LOCAL_LIB}" "${PERL_MODULES[@]}"
  elif [[ "${DRY_RUN}" -eq 1 ]]; then
    log "Dry-run: would download ${CPANM_URL} and run" \
      "'perl cpanm --notest --local-lib ${PERL_LOCAL_LIB} ${PERL_MODULES[*]}'."
    return
  else
    local workdir
    workdir="$(mktemp -d)"
    run_cmd curl -fsSL -o "${workdir}/cpanm" "${CPANM_URL}"
    run_cmd perl "${workdir}/cpanm" --notest --local-lib "${PERL_LOCAL_LIB}" "${PERL_MODULES[@]}"
    rm -rf "${workdir}"
  fi

  if [[ "${DRY_RUN}" -eq 0 ]] && ! perl_modules_available; then
    log "❌ Failed to install po4a's Perl modules (${PERL_MODULES[*]})."
    exit 1
  fi
}

install_texlive_packages() {
  log "--- 🇯🇵 Installing TeX Live packages ---"
  install_repo_texlive
  if [[ -n "${TLMGR_REPOSITORY}" ]]; then
    log "Pinning TeX Live package repository: ${TLMGR_REPOSITORY}"
    run_tex_cmd tlmgr option repository "$(texlive_repository_url)"
  fi
  # A restored cache may contain older packages from the previous snapshot.
  run_tex_cmd tlmgr update --self --all
  run_tex_cmd tlmgr install "${TEXLIVE_PACKAGES[@]}"
  run_tex_cmd luaotfload-tool --update --force
}

provision_lean() {
  if [[ "${PROVISION_LEAN}" != "1" ]]; then
    log "--- 🧮 Skipping Lean toolchain provisioning (PROVISION_LEAN=${PROVISION_LEAN}) ---"
    return
  fi

  local toolchain
  toolchain="$(tr -d '[:space:]' <lean-toolchain 2>/dev/null || true)"
  if [[ -z "${toolchain}" ]]; then
    log "⚠️  lean-toolchain is missing or empty; skipping Lean toolchain provisioning."
    return
  fi

  log "--- 🧮 Provisioning the pinned Lean toolchain (${toolchain}) ---"
  local elan
  if ! ensure_elan || ! elan="$(elan_bin)"; then
    log "⚠️  Failed to install elan; Lean-based tooling will be"
    log "    unavailable until elan is installed and '${toolchain}' is provisioned."
    return
  fi

  local installed_toolchains
  installed_toolchains="$("${elan}" toolchain list 2>/dev/null)" || true
  if printf '%s\n' "${installed_toolchains}" | grep -qF "${toolchain}"; then
    log "Lean toolchain ${toolchain} already installed."
    return
  fi

  # Best-effort: the PDF book build does not need Lean, so a failure here does
  # not abort setup. mathlib stays lazy and is fetched on the first `lake build`.
  if ! run_cmd "${elan}" toolchain install "${toolchain}"; then
    log "⚠️  Failed to provision the Lean toolchain; Lean-based tooling will be"
    log "    unavailable until '${elan} toolchain install ${toolchain}' succeeds."
  fi
}

# Drop any ghc/cabal install that mise cannot resolve a runnable bin for, so the
# subsequent `mise install` rebuilds it through the ghcup plugin registered
# above. mise's default `ghc`/`cabal` backend is conda, and a conda-installed
# cabal lands at <install>/cabal with no bin/ subdirectory, where `mise exec --
# cabal` fails with "couldn't exec process: No such file or directory". mise
# never reinstalls an already-present version, so such a stale conda-layout
# install — left over from a checkout provisioned before the ghcup plugin was
# adopted — is otherwise never replaced. A healthy ghcup install resolves fine
# and is left untouched; a not-yet-installed tool has no `mise where` path and
# is likewise skipped (the `mise install` below installs it fresh).
heal_ghcup_backend() {
  local tool mise
  mise="$(mise_cmd)"
  for tool in ghc cabal; do
    if "${mise}" where "${tool}" >/dev/null 2>&1 &&
      ! "${mise}" which "${tool}" >/dev/null 2>&1; then
      log "--- ♻️  Reinstalling ${tool} via ghcup (unusable non-ghcup layout detected) ---"
      run_mise uninstall "${tool}"
    fi
  done
}

run_doctor() {
  log "--- 🔎 Checking repository setup ---"

  set_mise_bin
  ensure_gettext_on_path
  if [[ -n "${MISE_BIN}" ]]; then
    doctor_ok "mise found at ${MISE_BIN}"
  else
    doctor_fail "mise found"
    log "Run './setup.sh --run' to install mise and the pinned toolchain."
    exit 1
  fi

  doctor_check "C compiler available" command -v cc
  doctor_check "make available" command -v make
  doctor_check "mise.toml present" test -f mise.toml
  doctor_mise_trust_check
  doctor_mise_check "GHC available through mise" ghc --version
  doctor_mise_check "cabal available through mise" cabal --version
  doctor_mise_check "Python available through mise" python --version
  doctor_mise_check "Pandoc available through mise" pandoc --version
  doctor_check "po4a >= ${PO4A_MIN_VERSION} available (mise http:po4a)" po4a_version_ok
  local perl_module
  for perl_module in "${PERL_MODULES[@]}"; do
    doctor_check "Perl module ${perl_module} available (.perllib)" perl_module_present "${perl_module}"
  done
  local gettext_command
  for gettext_command in "${GETTEXT_COMMANDS[@]}"; do
    doctor_check "GNU gettext ${gettext_command} --version succeeds" gettext_version_available "${gettext_command}"
  done
  doctor_tex_check "LuaLaTeX available" lualatex --version
  doctor_tex_check "latexdiff available" latexdiff --version
  doctor_tex_available_check "makeindex available" makeindex
  doctor_tex_available_check "upmendex available (Japanese index builds)" upmendex
  doctor_tex_check "LuaTeX-ja package available" kpsewhich luatexja.sty
  doctor_tex_check "xkeyval package available (required by LuaTeX-ja)" kpsewhich xkeyval.sty
  doctor_tex_check "selnolig package available (required by Pandoc's LuaTeX template)" kpsewhich selnolig.sty
  doctor_tex_check "Harano Aji Japanese font available" kpsewhich HaranoAjiMincho-Regular.otf
  # The Makefile pipes every LuaLaTeX run through texfot; PDF builds fail without it.
  doctor_tex_available_check "texfot available (required: PDF builds pipe LuaLaTeX through it)" texfot
  doctor_mise_check "Node available through mise" node --version
  doctor_mise_check "TypeScript (tsc) available through mise" tsc --version
  doctor_mise_check "esbuild available through mise" esbuild --version
  doctor_mise_check "tree-sitter available through mise" tree-sitter --version
  doctor_mise_check "watchexec available through mise" watchexec --version
  doctor_mise_check "lefthook available through mise" lefthook version
  doctor_lefthook_hook_check
  doctor_tex_check "tlmgr available" tlmgr --version
  doctor_tex_check "luaotfload-tool available" luaotfload-tool --version
  doctor_elan_check
  doctor_lean_toolchain_check

  if [[ "${doctor_failed}" -eq 0 ]]; then
    log "--- ✅ Setup check passed. ---"
  else
    log "--- ❌ Setup check failed. Run './setup.sh --run' and then retry 'make doctor'. ---"
    exit 1
  fi
}

if [[ "${DOCTOR}" -eq 1 ]]; then
  run_doctor
  exit 0
fi

if [[ "${DRY_RUN}" -eq 1 ]]; then
  log "--- Dry-run mode: commands will be printed, not run. Use --run to install. ---"
fi

# In a linked git worktree, clone the main checkout's gitignored caches
# (.texlive/, */.lake/, build/ dirs) before provisioning anything, so the TeX
# Live install below sees the tree as already present instead of downloading
# it again. The clone is copy-on-write where the filesystem supports it and a
# no-op in the main checkout or when the caches already exist; see
# tools/worktree_caches.sh.
if [[ -x tools/worktree_caches.sh ]]; then
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    tools/worktree_caches.sh --dry-run
  else
    tools/worktree_caches.sh
  fi
fi

case "$(uname -s)" in
Darwin)
  install_macos
  ;;
Linux)
  install_linux
  ;;
*)
  log "❌ Unsupported operating system: $(uname -s)"
  exit 1
  ;;
esac

install_translation_tools

set_mise_bin
if [[ -z "${MISE_BIN}" && "${DRY_RUN}" -eq 0 ]]; then
  log "❌ Required command not found: mise"
  exit 1
fi

# Put the mise binary's directory on PATH for the rest of setup. We otherwise
# call mise by absolute path, but mise's npm backend (npm:typescript,
# npm:esbuild) installs through node's npm, which is itself a mise shim that
# re-invokes the bare `mise` command. On a fresh install ~/.local/bin is not yet
# on PATH, so that shim fails with "mise: command not found" and the npm backend
# aborts ("mise ERROR npm failed"). Making `mise` resolvable on PATH fixes it.
if [[ -n "${MISE_BIN}" ]]; then
  mise_dir="$(dirname "${MISE_BIN}")"
  case ":${PATH}:" in
  *":${mise_dir}:"*) ;;
  *)
    PATH="${mise_dir}:${PATH}"
    export PATH
    ;;
  esac
fi

log "--- 🛡 Setting up mise-managed tools ---"
run_mise trust
# Pin GHC and cabal to the ghcup backend before installing. mise's `ghc`/`cabal`
# registry entries default to the conda backend, whose package set is
# platform-spotty: conda-forge has no ghc 9.14.1 for linux-x64, so a plain
# `mise install` fails there with "conda solve failed: No candidates were found
# for ghc ==9.14.1" (it works on macOS only because conda happens to carry it).
# ghcup is the canonical, cross-platform GHC installer and carries the pinned
# ghc/cabal on both macOS and Linux. Installing the plugin under the tool name
# (`ghc`, `cabal`) makes mise prefer it over the conda registry default — the
# plugin keys off that name when it runs `ghcup list/install -t <name>`.
# Re-installing an already-present plugin is a no-op, so this stays idempotent.
run_mise plugin install --yes ghc https://github.com/mise-plugins/mise-ghcup
run_mise plugin install --yes cabal https://github.com/mise-plugins/mise-ghcup
heal_ghcup_backend
run_mise install

log "--- 🪝 Installing git hooks (lefthook) ---"
run_mise exec -- lefthook install
harden_lefthook_hooks

install_texlive_packages

provision_lean

log "--- 🔎 Checking TeX commands ---"
run_tex_cmd lualatex --version
run_tex_cmd latexdiff --version
check_tex_cmd_available makeindex

log "--- 📚 Updating Cabal Package Index ---"
run_mise exec -- cabal update

run_mise exec -- pandoc --version

log "--- ✨ Setup Complete! ---"
log "Next steps:"
log "1. Run 'make' to build the books."
log "2. Optional: add mise shell activation if you want to run tools like pandoc directly outside make."
