#!/bin/bash
# leancheck -- the full AFM Lean battery for ONE repo, in one command.
#   usage: runall.sh <repo-dir> [--fast]     (--fast skips the slow local-model 2b pass)
# Layers: 1 gate, 2 tamper, 4 mutations, 5 contradiction, 6 ablation, 7 linter, 8 satisfiability,
#         9 bridge inventory.  Layers 10-12 (bridges, name/line anchors, prose review) are per-paper.
set -u
REPO="${1:?usage: runall.sh <repo-dir> [--fast]}"
FAST="${2:-}"
TS=$(date -u +%Y%m%d_%H%M%S)
mkdir -p "$HOME/leancheck/reports" "$HOME/leancheck/out/$REPO"
REPORT="$HOME/leancheck/reports/${REPO}_${TS}.md"
exec > "$HOME/leancheck/reports/${REPO}_${TS}.log" 2>&1
echo "LEANCHECK $REPO $(date -u)"
cd "$HOME/$REPO" || { echo "NO REPO $REPO"; exit 1; }
{
echo "# leancheck — $REPO ($(date -u '+%Y-%m-%d %H:%M UTC'))"
echo
echo "- path: $HOME/$REPO"
echo "- HEAD: $(git rev-parse HEAD 2>/dev/null || echo 'not a git repo')"
echo "- uncommitted entries: $(git status --porcelain 2>/dev/null | wc -l)"
echo
echo "## Layers 1-2 — gate and tamper"
echo '```'
} > "$REPORT"
if [ -f gate.sh ]; then
  bash gate.sh 2>&1 | tail -3 | tee -a "$REPORT"
  bash tests/tamper.sh 2>&1 | tail -12 | tee -a "$REPORT"
else
  echo "NO gate.sh — layers 1-2 NOT run" | tee -a "$REPORT"
fi
echo '```' >> "$REPORT"
echo "## Layers 4,5,8 — mutations, contradiction probe, satisfiability" >> "$REPORT"
ARC="$HOME/leancheck/archive/${REPO}_pre_${TS}"; mkdir -p "$ARC"
[ -f "$HOME/leancheck/out/$REPO/results.jsonl" ] && mv "$HOME/leancheck/out/$REPO/results.jsonl" "$ARC/"
rm -f "$HOME/leancheck/out/$REPO/summary.md" "$HOME/leancheck/out/$REPO/lint.json" "$HOME/leancheck/out/$REPO/lint_scratch.json"
python3 "$HOME/leancheck/mkmod.py" "$REPO" $FAST >/dev/null
{ cd "$HOME/lc_mod" && python3 lc_mod.py; } 2>&1 | tail -4
if [ -f "$HOME/leancheck/out/$REPO/summary.md" ]; then
  sed -n '1,200p' "$HOME/leancheck/out/$REPO/summary.md" >> "$REPORT"
fi
echo "## Layers 6,9 — hypothesis ablation and bridge inventory" >> "$REPORT"
echo "## Layer 7 — unused-variable linter" >> "$REPORT"
python3 "$HOME/leancheck/lintlib.py" | tee -a "$REPORT"
python3 "$HOME/leancheck/lintscratch.py" "$REPO" | tee -a "$REPORT"
echo >> "$REPORT"; echo "## Verdict" >> "$REPORT"
python3 "$HOME/leancheck/verdict.py" "$REPO" | tee -a "$REPORT"
echo "== REPORT $REPORT"
echo "LEANCHECK DONE $(date -u)" | tee -a "$REPORT"
