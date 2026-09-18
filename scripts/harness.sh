#!/usr/bin/env bash
# scripts/harness.sh — JSP-000415 verification harness.
# Runs lake build, counts sorry/admit, dumps #print axioms of the headline
# theorem, and appends a timestamped verdict to HARNESS_LOG.md.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

LOG=HARNESS_LOG.md
SHA=$(git rev-parse HEAD 2>/dev/null || echo "none")
TS=$(date -u +%Y-%m-%dT%H:%M:%SZ)

OUT=$(mktemp)
{
  echo "---"
  echo "## Run $TS"
  echo
  echo "- commit: \`$SHA\`"
  echo
  echo '### lake build'
  echo '```'
} >> "$OUT"

(cd lean && lake build) >> "$OUT" 2>&1
BUILD=$?
echo '```' >> "$OUT"
echo "- build_exit_code: **$BUILD**" >> "$OUT"
echo >> "$OUT"

echo '### sorry / admit occurrences (excluding .lake)' >> "$OUT"
echo '```' >> "$OUT"
grep -rIn --include='*.lean' -E '\b(sorry|admit)\b' --exclude-dir=.lake lean >> "$OUT" 2>&1
SORRY=$(grep -rIn --include='*.lean' -E '\b(sorry|admit)\b' --exclude-dir=.lake lean | wc -l | tr -d ' ')
echo '```' >> "$OUT"
echo "- sorry_admit_occurrences: **$SORRY**" >> "$OUT"
echo >> "$OUT"

echo '### #print axioms monochromatic_path_cover' >> "$OUT"
echo '```' >> "$OUT"
cat > lean/AxiomCheck.lean <<'EOF'
import JSP415
#print axioms JSP415.monochromatic_path_cover
EOF
if [ "$BUILD" = 0 ]; then
  (cd lean && lake env lean AxiomCheck.lean) >> "$OUT" 2>&1
else
  echo "skipped (build failed)" >> "$OUT"
fi
rm -f lean/AxiomCheck.lean
echo '```' >> "$OUT"
echo >> "$OUT"

if [ "$BUILD" = 0 ] && [ "$SORRY" = 0 ]; then
  echo "### RESULT: GREEN" >> "$OUT"
else
  echo "### RESULT: RED" >> "$OUT"
fi
echo >> "$OUT"

cat "$OUT" >> "$LOG"
cat "$OUT"
rm -f "$OUT"
