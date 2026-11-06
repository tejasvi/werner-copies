#!/bin/bash
# one exact-worker job: run_worker.sh PRIME FAMILY CHUNK NCHUNK   (called by run_all.sh; logs in logs/)
cd "$(dirname "$0")/.."
PY=${PYTHON:-python3}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
exec $PY -I verify/exact_words.py "$1" "$2" "$3" "$4" work/orb "work/res/res_p$1_f$2_c$3.npz" > "logs/w_p$1_f$2_c$3.log" 2>&1
