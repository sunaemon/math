#!/usr/bin/env bash
#
# Refresh the tree-sitter assets vendored under
# tools/formalization-viewer/vendor/treesitter/. These files are committed, so the
# formalization viewer does not need this script to run; use it only to update or
# re-pin the runtime, grammars, and highlight queries.
#
# Produces:
#   web-tree-sitter.js / web-tree-sitter.wasm     runtime (npm web-tree-sitter)
#   tree-sitter-markdown.wasm                      block grammar (GH release)
#   tree-sitter-markdown_inline.wasm               inline grammar (GH release)
#   tree-sitter-lean.wasm                          built from Julian/tree-sitter-lean
#   queries/{markdown,markdown_inline,lean}.scm    highlights.scm from each grammar
#   VERSIONS                                       pinned versions and lean commit
#
# The tree-sitter CLI (for building the Lean grammar to Wasm) comes from mise.
# `tree-sitter build --wasm` falls back to the emsdk Docker image when emcc is
# not on PATH, so a running Docker daemon is required for the Lean build.

set -euo pipefail

# --- Pinned versions -------------------------------------------------------
WEB_TREE_SITTER_VERSION="0.26.9"
MARKDOWN_VERSION="0.5.3"
LEAN_COMMIT="463a9d8a509c935f4e10854b5078bbe2839b274c"
# ---------------------------------------------------------------------------

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
VENDOR_DIR="${REPO_ROOT}/tools/formalization-viewer/vendor/treesitter"
QUERIES_DIR="${VENDOR_DIR}/queries"

log() {
  echo "--- $* ---" >&2
}

tree_sitter() {
  if command -v tree-sitter >/dev/null 2>&1; then
    tree-sitter "$@"
  elif command -v mise >/dev/null 2>&1; then
    mise exec -- tree-sitter "$@"
  else
    echo "tree-sitter CLI not found; install it via 'mise install'." >&2
    exit 1
  fi
}

WORK_DIR="$(mktemp -d)"
cleanup() {
  rm -rf "${WORK_DIR}"
}
trap cleanup EXIT

mkdir -p "${VENDOR_DIR}" "${QUERIES_DIR}"

# --- 1. web-tree-sitter runtime (npm) --------------------------------------
log "Fetching web-tree-sitter ${WEB_TREE_SITTER_VERSION} runtime"
curl -fsSL \
  "https://registry.npmjs.org/web-tree-sitter/-/web-tree-sitter-${WEB_TREE_SITTER_VERSION}.tgz" |
  tar -xz -C "${WORK_DIR}"
# A committed, hand-written web-tree-sitter.d.ts sits next to the runtime so
# `tsc` skips the bundled .js; it is intentionally not refreshed here. If the
# runtime's exported names ever change, update that shim by hand.
cp "${WORK_DIR}/package/web-tree-sitter.js" "${VENDOR_DIR}/web-tree-sitter.js"
cp "${WORK_DIR}/package/web-tree-sitter.wasm" "${VENDOR_DIR}/web-tree-sitter.wasm"

# --- 2. Markdown grammars (prebuilt Wasm from GH release) ------------------
log "Fetching tree-sitter-markdown ${MARKDOWN_VERSION} Wasm modules"
markdown_release="https://github.com/tree-sitter-grammars/tree-sitter-markdown/releases/download/v${MARKDOWN_VERSION}"
curl -fsSL "${markdown_release}/tree-sitter-markdown.wasm" \
  -o "${VENDOR_DIR}/tree-sitter-markdown.wasm"
curl -fsSL "${markdown_release}/tree-sitter-markdown_inline.wasm" \
  -o "${VENDOR_DIR}/tree-sitter-markdown_inline.wasm"

log "Fetching tree-sitter-markdown highlight queries"
markdown_raw="https://raw.githubusercontent.com/tree-sitter-grammars/tree-sitter-markdown/v${MARKDOWN_VERSION}"
curl -fsSL "${markdown_raw}/tree-sitter-markdown/queries/highlights.scm" \
  -o "${QUERIES_DIR}/markdown.scm"
curl -fsSL "${markdown_raw}/tree-sitter-markdown-inline/queries/highlights.scm" \
  -o "${QUERIES_DIR}/markdown_inline.scm"

# --- 3. Lean grammar (build Wasm from source) ------------------------------
log "Cloning Julian/tree-sitter-lean @ ${LEAN_COMMIT}"
lean_dir="${WORK_DIR}/tree-sitter-lean"
git clone --quiet https://github.com/Julian/tree-sitter-lean "${lean_dir}"
git -C "${lean_dir}" checkout --quiet "${LEAN_COMMIT}"

log "Building tree-sitter-lean.wasm (emcc via Docker fallback)"
tree_sitter build --wasm --output "${VENDOR_DIR}/tree-sitter-lean.wasm" "${lean_dir}"
cp "${lean_dir}/queries/highlights.scm" "${QUERIES_DIR}/lean.scm"

# --- 4. VERSIONS record ----------------------------------------------------
cat >"${VENDOR_DIR}/VERSIONS" <<EOF
web-tree-sitter ${WEB_TREE_SITTER_VERSION}
tree-sitter-markdown v${MARKDOWN_VERSION}
tree-sitter-lean ${LEAN_COMMIT}
EOF

log "Vendored tree-sitter assets into ${VENDOR_DIR}"
ls -1 "${VENDOR_DIR}" "${QUERIES_DIR}" >&2
