#!/usr/bin/env bash
# Delete an unusable derived setup cache, never a source tree or external path.
set -euo pipefail
if [[ "$#" -ne 2 ]]; then
  echo "Usage: bash tools/remove_setup_cache.sh REPOSITORY CACHE_DIRECTORY" >&2
  exit 2
fi
repo_root="$(cd "$1" && pwd -P)"
cache_root="$(cd "$2" && pwd -P)"
case "${cache_root}" in
"${repo_root}"/*) ;;
*)
  echo "Refusing to remove cache outside the repository or the repository root: ${cache_root}" >&2
  exit 1
  ;;
esac
relative="${cache_root#"${repo_root}/"}"
case "${relative}" in
.git | .git/* | .codex | .codex/* | .claude | .claude/* | .agents | .agents/* | .aws | .aws/*)
  echo "Refusing to remove repository metadata: ${cache_root}" >&2
  exit 1
  ;;
esac
tracked="$(git --literal-pathspecs -C "${repo_root}" ls-files -- "${relative}")"
if [[ -n "${tracked}" ]]; then
  echo "Refusing to remove a cache containing tracked source files: ${cache_root}" >&2
  exit 1
fi
rm -rf -- "${cache_root}"
