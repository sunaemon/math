#!/usr/bin/env bash
# Poll a GitHub PR until it is merged (or closed), then exit. Intended to drive
# the PR-per-iteration loop: run it in the background and the harness re-invokes
# the agent the moment the PR's state resolves, instead of waiting on a fixed timer.
#
# Usage: tools/wait-pr-merged.sh <pr-number> [poll-seconds] [max-minutes]
#   exit 0  -> merged
#   exit 2  -> closed without merging
#   exit 3  -> timed out
#   exit 64 -> bad usage
set -euo pipefail

pr="${1:-}"
interval="${2:-60}"
max_minutes="${3:-720}"

if [[ -z "$pr" ]]; then
  echo "usage: $0 <pr-number> [poll-seconds] [max-minutes]" >&2
  exit 64
fi

deadline=$(($(date +%s) + max_minutes * 60))

while :; do
  # state is OPEN | MERGED | CLOSED; mergedAt is null until merged.
  read -r state merged_at < <(gh pr view "$pr" --json state,mergedAt \
    --jq '[.state, (.mergedAt // "null")] | @tsv' 2>/dev/null || echo "QUERY_FAILED null")

  ts="$(date '+%H:%M:%S')"
  case "$state" in
  MERGED)
    echo "[$ts] PR #$pr MERGED (mergedAt=$merged_at)"
    exit 0
    ;;
  CLOSED)
    echo "[$ts] PR #$pr CLOSED without merge"
    exit 2
    ;;
  OPEN)
    echo "[$ts] PR #$pr still open; re-checking in ${interval}s"
    ;;
  *)
    echo "[$ts] gh query failed or unknown state ('$state'); retrying in ${interval}s" >&2
    ;;
  esac

  if (($(date +%s) >= deadline)); then
    echo "[$ts] timed out after ${max_minutes}m waiting on PR #$pr" >&2
    exit 3
  fi
  sleep "$interval"
done
