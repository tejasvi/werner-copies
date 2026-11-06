#!/bin/bash
# Exact checks for Section 9 of the accompanying paper: Theorem 9.2 (q_k(11/(5k)) >= 0 for k >= 6 and q_k(56/(25k)) >= 0
# for k >= 9, every d), the exact thresholds gamma_6 and gamma_7, the numerical parts of Proposition 9.3(a), and the
# identities and numerical checks of Section 10.6 (Theorem 10.7).
# Usage: ./run_all.sh            Optional: REGEN=1 re-derives the two all-k certificates from the LP (work/) and re-checks them.
set -euo pipefail
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p logs work
echo "== 0. checksums"; sha256sum -c SHA256SUMS --quiet && echo "SHA256SUMS OK"
echo "== 1. all-k certificates of Theorem 9.2 (exact rational check, no LP)"
$PY -I code/allk_check.py certs/allk_k5_X2.2.json  | tee logs/allk_check_X2.2.log
$PY -I code/allk_check.py certs/allk_k5_X2.24.json | tee logs/allk_check_X2.24.log
echo "== 1b. negative control: without input (I6) the checker must refuse the same file"
if $PY -I code/allk_check.py certs/allk_k5_X2.2.json --no-k5 > work/allk_check_no_k5.out 2>&1; then
  echo "NEGATIVE CONTROL FAILED"; exit 1
else
  echo "refused as expected: $(tail -1 work/allk_check_no_k5.out)" | tee logs/allk_check_no_k5.log
fi
echo "== 2. exact thresholds gamma_6, gamma_7 (parametric certificates, then an independent label-based re-check)"
$PY -I code/cert_k5.py all:6:0.3686833860 all:7:0.3180764683 | tee logs/cert_k5.log
$PY -I code/verify_k5_certs.py logs/cert_k5.log | tee logs/verify_k5_certs.log
echo "== 3. Proposition 9.3(a): Claim 1 (exact rationals and interval bound), Claim 2 constant, sanity checks"
$PY -I code/expo_k5.py 1/200 40 300 | tee logs/expo_k5.log
echo "== 4. limit LP thresholds c*_J (floating point; they increase towards 9/4)"
$PY -I code/limit_lp_k5.py 8,10,12,14,16 | tee logs/limit_lp_k5.log
echo "== 5. independent construction (own code, own large-k argument)"
$PY -I independent/a_cert_v2.py 11/5 12 6        | tee logs/a_cert_v2_X2.2_J12.log
$PY -I independent/a_cert_v2.py 56/25 14 9       | tee logs/a_cert_v2_X2.24_J14.log
$PY -I independent/a_cert_v3.py 11/5 12 6 notbc  | tee logs/a_cert_v3_X2.2_J12_notbc.log
$PY -I independent/a_cert_v3.py 56/25 14 9 notbc | tee logs/a_cert_v3_X2.24_J14_notbc.log
$PY -I independent/a_controls.py                 | tee logs/a_controls.log
$PY -I independent/b_check_v2.py                 | tee logs/b_check_v2.log
echo "== 6. Section 10.6: the identities of Theorem 10.7 (sympy) and numerical checks of its proof"
$PY -I sec10/check_sec10.py | tee logs/check_sec10.log
if [ "${REGEN:-0}" = 1 ]; then
  echo "== 7. regenerate the all-k certificates from the LP and re-check them"
  $PY -I code/allk_dump.py 11/5 12 6 work/allk_k5_X2.2.json --k5  | tee logs/allk_dump_X2.2.log
  $PY -I code/allk_dump.py 56/25 14 9 work/allk_k5_X2.24.json --k5 | tee logs/allk_dump_X2.24.log
  $PY -I code/allk_check.py work/allk_k5_X2.2.json  | tee logs/allk_check_regen_X2.2.log
  $PY -I code/allk_check.py work/allk_k5_X2.24.json | tee logs/allk_check_regen_X2.24.log
fi
echo "== verdict"
fail=0
need() { if ! grep -q -- "$2" "logs/$1"; then echo "MISSING in $1: $2"; fail=1; fi; }
none() { if grep -q -- "$2" "logs/$1"; then echo "UNEXPECTED in $1: $2"; fail=1; fi; }
need allk_check_X2.2.log  "ALL CHECKS PASS: q_k(11/5/k) >= 0 for every k >= 6"
need allk_check_X2.24.log "ALL CHECKS PASS: q_k(56/25/k) >= 0 for every k >= 9"
need allk_check_no_k5.log "refused as expected: AssertionError: K5 row refused"
[ "$(grep -c 'CERTIFIED True' logs/cert_k5.log)" = 2 ] || { echo "cert_k5: expected 2 certified thresholds"; fail=1; }
need verify_k5_certs.log "ALL PASS"
need expo_k5.log "CLAIM 1 (bt_r >= 0 for 2 <= r <= k, all k >= 40, all eps in (0, 1/200]): True"
need a_cert_v2_X2.2_J12.log        "ALL k >= 6 CERTIFIED"
need a_cert_v2_X2.24_J14.log       "ALL k >= 9 CERTIFIED"
need a_cert_v3_X2.2_J12_notbc.log  "ALL k >= 6 CERTIFIED"
need a_cert_v3_X2.24_J14_notbc.log "ALL k >= 9 CERTIFIED"
need a_controls.log "CONTROLS DONE"
[ "$(grep -c 'FAILS as it must' logs/a_controls.log)" = 5 ] || { echo "a_controls: expected 5 failing negative controls"; fail=1; }
none a_controls.log "NEGATIVE"
none a_controls.log "UNEXPECTED PASS"
need b_check_v2.log "B_CHECK DONE"
none b_check_v2.log "FAIL"
[ "$(grep -c '^OK (' logs/check_sec10.log)" = 5 ] || { echo "check_sec10: expected 5 symbolic identities"; fail=1; }
need check_sec10.log "OK Part B (all minima >= -1e-9)"
if [ "${REGEN:-0}" = 1 ]; then
  need allk_check_regen_X2.2.log  "ALL CHECKS PASS"
  need allk_check_regen_X2.24.log "ALL CHECKS PASS"
fi
if [ "$fail" = 0 ]; then echo "ALL-K CHECKS PASSED: Theorem 9.2, gamma_6, gamma_7, the numerical parts of Proposition 9.3(a) and the checks of Section 10.6"
else echo "ALL-K CHECKS FAILED"; exit 1; fi
