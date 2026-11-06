#!/bin/bash
# Exact end-to-end check of Theorem K4 (rho(d, alpha) is 4-copy undistillable for alpha >= -79/160 in every d).
# Usage: ./run_all.sh [NPROC]      NPROC = parallel exact-worker jobs (default 8; 54 jobs in total)
# Optional: REFIT_LAMBDA=1 (re-derive lam, ~12 min, ~25 GB RAM), RUN_E2E=1 (physical-point sanity check),
#           RUN_FLOAT=1 (word_rig_v2 float cross-check, ~15 min + NPROC worker processes).
set -euo pipefail
cd "$(dirname "$0")"
NPROC=${1:-8}
PY=${PYTHON:-python3}
export PYTHON=$PY OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p work/res logs
echo "== 0. checksums"; sha256sum -c SHA256SUMS --quiet && echo "SHA256SUMS OK"
echo "== 1. exact trace-slack constant LK";       $PY -I verify/lk_exact.py  | tee logs/lk_exact.log
echo "== 2. multiplier factors from the certificate"; $PY -I verify/prep_m.py | tee logs/prep_m.log
echo "== 3. equality structure and lam";          $PY -I verify/prep_eq.py   | tee logs/prep_eq.log
echo "== 4. orbit labels";                        $PY -I verify/orbits.py    | tee logs/orbits.log
echo "== 5. S2 upper bound";                      $PY -I verify/s2_bound.py  | tee logs/s2.log
echo "== 6. exact residues: 18 primes x 3 chunks, $NPROC in parallel (logs/w_*.log)"
for p in $(cat verify/primes.txt); do for c in 0 1 2; do echo "$p $c"; done; done \
  | xargs -P "$NPROC" -L 1 sh -c 'verify/run_worker.sh "$0" "$1" 3'
echo "== 7. CRT combination and margin"
$PY -I verify/combine.py s2_bound.pkl combined.pkl 'res/res_p*_c*.pkl' | tee logs/combine.log
if [ "${RUN_E2E:-0}" = 1 ]; then echo "== 8. physical-point sanity check"; $PY -I verify/e2e_check.py 1 | tee logs/e2e_1.log; fi
if [ "${RUN_FLOAT:-0}" = 1 ]; then
  echo "== 9. float cross-check (word_rig_v2)"
  $PY -I crosscheck/word_rig_v2.py certs/exact_types_k4_d4.pkl certs/ns_ident_k4.pkl certs/ipm_s0_gp_t79_160.pkl \
      certs/meta_margin_t79_160_slim.pkl 8e-10 "$NPROC" work/wrig2_t79_160.pkl | tee logs/wrig2_t79_160.log
fi
if grep -q "=> POSITIVE" logs/combine.log; then echo "K4 EXACT CHECK PASSED: margin positive for every d >= 1.25e9 (all d by Lemma M1)"
else echo "K4 EXACT CHECK FAILED"; exit 1; fi
