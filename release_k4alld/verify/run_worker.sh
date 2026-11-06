#!/bin/bash
# one exact-worker job: run_worker.sh PRIME CHUNK NCHUNK   (called by run_all.sh; logs in logs/)
cd "$(dirname "$0")/.."
PY=${PYTHON:-python3}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
exec $PY -I verify/exact_worker.py "$1" "res/res_p$1_c$2.pkl" "$3" "$2" > "logs/w_p$1_c$2.log" 2>&1
