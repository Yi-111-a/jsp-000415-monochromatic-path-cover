#!/usr/bin/env bash
# scripts/status.sh — structured status output for JSP-000415.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

SHA=$(git rev-parse HEAD 2>/dev/null || echo "none")
SORRY=$(grep -rIn --include='*.lean' -E '\b(sorry|admit)\b' --exclude-dir=.lake lean | wc -l | tr -d ' ')
SORRY_FILES=$(grep -rIl --include='*.lean' -E '\b(sorry|admit)\b' --exclude-dir=.lake lean | sed 's|^|\"|;s|$|\"|' | paste -sd, -)
THMS=$(grep -rIn --include='*.lean' -cE '^[[:space:]]*(theorem|lemma)' --exclude-dir=.lake lean | awk -F: '{s+=$2} END{print s+0}')
OLEAN=$(find lean/.lake/build/lib -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')
LAST_LOG=0
[ -f HARNESS_LOG.md ] && LAST_LOG=$(grep -c 'RESULT: GREEN' HARNESS_LOG.md || true)

cat <<EOF
{
  "jsp_id": "JSP-000415",
  "commit": "$SHA",
  "theorems_lemmas_total": $THMS,
  "sorry_admit_occurrences": $SORRY,
  "sorry_files": [$SORRY_FILES],
  "built_olean_files": $OLEAN,
  "green_runs_in_log": $LAST_LOG,
  "headline": "JSP415.monochromatic_path_cover"
}
EOF
