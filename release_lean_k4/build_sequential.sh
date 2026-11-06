#!/usr/bin/env bash
# build_sequential.sh [MODULE ...]: memory-safe build of this package, one module at a time (see README_k4.md).
#
#   ./build_sequential.sh                    every module of build_order.txt, then the axioms of the main theorems
#   ./build_sequential.sh NPT.K4.Final497    only the given modules and their imports (needs python3)
#
# Runs `lake build <module>` for one module at a time, in topological import order (imports first), so at most one
# Lean process runs: several data modules need tens of GB of memory each (README_k4.md, Building), and plain
# `lake build` would run many of them at once. Fetches the prebuilt Mathlib first (`lake exe cache get`, needs network
# access).
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake exe cache get
if [ $# -gt 0 ]; then
  order=$(python3 scripts/topo_order.py . "$@")
else
  order=$(cat build_order.txt)
fi
n=$(printf '%s\n' "$order" | wc -l)
i=0
t0=$(date +%s)
while IFS= read -r m; do
  i=$((i + 1))
  t=$(date +%s)
  lake build "$m"
  echo "[$i/$n] $m: $(( $(date +%s) - t )) s"
done <<< "$order"
echo "built $n modules in $(( $(date +%s) - t0 )) s"
if [ $# -eq 0 ]; then
  lake env lean NPT/K4/Axioms.lean
fi
