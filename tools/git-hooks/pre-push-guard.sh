#!/usr/bin/env bash
# pre-push guard: reject pushes that update the remote `main` branch directly,
# nudging toward a pull-request workflow. Wired through lefthook (pre-push), which
# forwards git's pre-push stdin: one line per pushed ref, of the form
#   <local ref> <local sha> <remote ref> <remote sha>
#
# This is a LOCAL convenience guard, not real enforcement: it only runs where
# lefthook is installed and is bypassable with `git push --no-verify`. Server-side
# branch protection (GitHub Pro / rulesets) is the real control.
set -u

protected_remote_ref="refs/heads/main"
blocked=0

while read -r _local_ref _local_sha remote_ref _remote_sha; do
  [ -z "${remote_ref}" ] && continue
  if [ "${remote_ref}" = "${protected_remote_ref}" ]; then
    blocked=1
  fi
done

if [ "${blocked}" -eq 1 ]; then
  cat >&2 <<'MSG'
✗ Direct pushes to main are disabled.
  Push a feature branch and open a pull request instead, e.g.:
      git switch -c my-change
      git push -u origin my-change
  Emergency bypass (use sparingly): git push --no-verify
MSG
  exit 1
fi

exit 0
