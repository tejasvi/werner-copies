#!/bin/bash
# second half of the exact chain (reduced re-solve, rounding, export) with a given IPM tolerance. Usage: chain_exact2.sh d tol
d=$1; tol=$2
PY=<ROOT>/cert/venv/bin/python
cd <ROOT>/dim
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8
EXACT_R=runs/exactR2_k3_d$d.pkl FORCE_DROP_ANOM=triv IPM_TOL=$tol $PY -I build_reduced.py 3,$d runs/exact_types2_k3_d$d.pkl runs/ratlin2_k3_d$d.pkl runs/sdp_k3_d$d.pkl runs/red2_k3_d$d.pkl > logs/red2_k3_d$d.log 2>&1 || exit 1
$PY -I run_exact.py 3,$d runs/exact_types2_k3_d$d.pkl runs/red2_k3_d$d.pkl runs/cert2_k3_d$d.pkl 120 > logs/cert2_k3_d$d.log 2>&1 || exit 1
export OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2
$PY -I export_cert.py runs/cert2_k3_d$d.pkl runs/certfile2_k3_d$d.pkl > logs/export2_k3_d$d.log 2>&1
$PY -I verify_cert.py runs/certfile2_k3_d$d.pkl > logs/verify2_k3_d$d.log 2>&1
echo chain2 done for d=$d
