#!/usr/bin/env bash
# codex-consult-safe.sh SPEC_FILE TOPIC
#
# Run a Codex consult on SPEC_FILE WITHOUT ever dumping the raw transcript
# into the terminal / Claude context. Raw output is archived to a file; only
# a bounded summary (markers + last 120 lines) is printed.
#
# NEVER `cat` a raw Codex output file. Use this wrapper for all consults.
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: $0 SPEC_FILE TOPIC" >&2
  exit 2
fi

SPEC="$1"
TOPIC="$2"
ROOT="$(git rev-parse --show-toplevel)"
OUTDIR="$ROOT/notes/codex-consults"
mkdir -p "$OUTDIR"

STAMP="$(date +%F-%H%M)"
RAW="$OUTDIR/${STAMP}-${TOPIC}-raw.txt"
SUMMARY="$OUTDIR/${STAMP}-${TOPIC}-summary.txt"

# Prepend an output contract so Codex keeps its visible answer terse. Even if
# it ignores this, the wrapper only ever exposes the bounded summary below.
CONTRACT='OUTPUT CONTRACT:
Your visible final answer must be at most 80 lines.
Start with exactly one of: PASS, WARN, BLOCK, PLAN.
Do not restate project background.
Do not paste long code excerpts, diffs, Lean terms, logs, or transcripts.
If detailed reasoning is useful, summarize it; do not dump it.
Give:
- verdict;
- exact recommended patch shape;
- files to edit;
- local lemmas needed;
- blockers, if any.

'

# `|| true`: keep going (and still emit a summary) even if codex exits nonzero.
codex exec "${CONTRACT}$(cat "$SPEC")" < /dev/null > "$RAW" 2>&1 || true

{
  echo "RAW: $RAW"
  echo "SUMMARY: $SUMMARY"
  echo
  echo "=== raw size ==="
  wc -l -c "$RAW"
  echo
  echo "=== extracted markers ==="
  grep -nE "^(PASS|WARN|BLOCK|PLAN|VERDICT|Verdict|Recommendation|Summary|Patch|Blocker|Next)" "$RAW" | tail -80 || true
  echo
  echo "=== final tail ==="
  tail -120 "$RAW"
} > "$SUMMARY"

echo "Codex consult complete."
echo "Raw log: $RAW"
echo "Summary: $SUMMARY"
echo "Raw size:"
wc -l -c "$RAW"
echo
echo "Summary tail:"
tail -120 "$SUMMARY"
