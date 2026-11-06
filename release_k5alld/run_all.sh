#!/bin/bash
# Exact end-to-end check of Theorem K5 (rho(d, alpha) is 5-copy undistillable for alpha >= -9/20 in every d).
# Usage: ./run_all.sh [NPROC]      NPROC = parallel exact-worker jobs (default 8; 240 jobs in total, about 5 GB RAM each)
# Optional: RUN_E2E=1   (physical-point checks on entangled rank-2 points, one process, about 25 min per n)
#           RUN_CROSS=1 (the producer's class-sum verifier as a cross-check; needs python-flint; about 12 min on 12 cores)
set -euo pipefail
cd "$(dirname "$0")"
NPROC=${1:-8}
PY=${PYTHON:-python3}
export PYTHON=$PY OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p work/res work/orb logs
echo "== 0. checksums"; sha256sum -c SHA256SUMS --quiet && echo "SHA256SUMS OK"
echo "== 1. exact trace-slack constant LK(1e10)";        $PY -I verify/lk5.py 1/10000000000 work/lk.pkl | tee logs/lk5.log
echo "== 2. per-site polynomial data vs exact local data"; $PY -I verify/ft_spot.py | tee logs/ft_spot.log
echo "== 3. word-level orbit labels (24^6 words, 3 families)"; $PY -I verify/orbits_words.py work/orb | tee logs/orbits.log
echo "== 4. absolute shadows: CRT bounds and the S2 majorant"; $PY -I verify/shadow_words.py work/shadow.pkl | tee logs/shadow.log
echo "== 5. exact residues: 10 primes x 3 families x 8 chunks, $NPROC in parallel (logs/w_*.log)"
for p in $(cat verify/primes.txt); do for f in 31 22 13; do for c in 0 1 2 3 4 5 6 7; do echo "$p $f $c"; done; done; done \
  | xargs -P "$NPROC" -L 1 sh -c 'verify/run_worker.sh "$0" "$1" "$2" 8'
echo "== 6. CRT combination and margin"
$PY -I verify/combine_words.py work/shadow.pkl work/lk.pkl 'work/res/*.npz' work/combined.pkl | tee logs/combine.log
if [ "${RUN_E2E:-0}" = 1 ]; then echo "== 7. physical-point checks (n = 4, 50, 1000, 1e10)"
  for n in 4 50 1000 1e10; do $PY -I verify/e2e5.py 1 $n all | tee logs/e2e5_1_n$n.log; done; fi
if [ "${RUN_CROSS:-0}" = 1 ]; then
  echo "== 8. cross-check: the producer's class-sum verifier"
  $PY -I crosscheck/verify_alld_k.py certs/k5_cert_t9_20.pkl 1/10000000000 "$NPROC" work/cross.pkl | tee logs/cross.log
fi
if grep -q "=> POSITIVE" logs/combine.log; then echo "K5 EXACT CHECK PASSED: margin positive for every d >= 1e10 (all d by zero padding)"
else echo "K5 EXACT CHECK FAILED"; exit 1; fi
