#!/bin/bash
# Verify EP_3 for every local dimension d >= 3:
#   per-dimension certificates d = 3..8 (verify_perd.py, up to PERD_JOBS in parallel), then
#   the all-dimension certificate for d >= 9 (verify_alld.py).
# Usage: ./run_all.sh [workers]          (default: number of cores; PERD_JOBS default 3; PYTHON default python3)
set -e
cd "$(dirname "$0")"
W=${1:-$(nproc)}
J=${PERD_JOBS:-3}
PY=${PYTHON:-python3}
export OMP_NUM_THREADS=${OMP_NUM_THREADS:-1} OPENBLAS_NUM_THREADS=${OPENBLAS_NUM_THREADS:-1}
mkdir -p logs
sha256sum -c SHA256SUMS
start=$(date +%s)
for d in 3 4 5 6 7 8; do
  $PY -I verify_perd.py certs/ep3_perd_d$d.pkl.xz --workers 2 > logs/perd_d$d.txt 2>&1 &
  while [ "$(jobs -rp | wc -l)" -ge "$J" ]; do sleep 2; done
done
wait
for d in 3 4 5 6 7 8; do grep -h "EXACT CERTIFICATE AT" logs/perd_d$d.txt; done
$PY -I verify_alld.py certs/ep3_alld.pkl.xz --workers "$W" 2>&1 | tee logs/alld.txt
echo "total wall time: $(( $(date +%s) - start )) s"
ok=1
for d in 3 4 5 6 7 8; do grep -q "EXACT CERTIFICATE AT d = $d: PASS" logs/perd_d$d.txt || ok=0; done
grep -q "ALL-D CERTIFICATE (d >= 9): PASS" logs/alld.txt || ok=0
if [ $ok = 1 ]; then echo "EP_3 VERIFIED FOR EVERY d >= 3"; else echo "VERIFICATION FAILED"; exit 1; fi
