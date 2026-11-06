#!/bin/bash
# full exact chain for the strengthened relaxation at dimension d: types, exact zero modes, exact R, linear kernels,
# exact-N reduced re-solve, exact rounding, export.  Usage: chain_exact.sh d
d=$1
PY=<ROOT>/cert/venv/bin/python
cd <ROOT>/dim
export OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2
[ -f runs/sdp_k3_d$d.pkl ] || $PY -I build_sdp.py 3 $d runs/sdp_k3_d$d.pkl > logs/build_k3_d$d.log 2>&1
$PY -I build_exact_types.py 3 $d runs/exact_types2_k3_d$d.pkl > logs/exact_types2_k3_d$d.log 2>&1
OMP_NUM_THREADS=1 $PY -I exact_zero_modes_fast.py $d 5 8 runs/ezm_k3_d$d.pkl $((300+d)) > logs/ezm_k3_d$d.log 2>&1
export OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4
$PY -I exact_R.py $d runs/ezm_k3_d$d.pkl runs/exactR2_k3_d$d.pkl > logs/exactR2_k3_d$d.log 2>&1
$PY -I make_rat_linear.py 3,$d runs/exact_types2_k3_d$d.pkl runs/sdp_k3_d$d.pkl runs/ratlin2_k3_d$d.pkl > logs/ratlin2_k3_d$d.log 2>&1
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8
EXACT_R=runs/exactR2_k3_d$d.pkl FORCE_DROP_ANOM=triv IPM_TOL=6e-9 $PY -I build_reduced.py 3,$d runs/exact_types2_k3_d$d.pkl runs/ratlin2_k3_d$d.pkl runs/sdp_k3_d$d.pkl runs/red2_k3_d$d.pkl > logs/red2_k3_d$d.log 2>&1
$PY -I run_exact.py 3,$d runs/exact_types2_k3_d$d.pkl runs/red2_k3_d$d.pkl runs/cert2_k3_d$d.pkl 120 > logs/cert2_k3_d$d.log 2>&1
export OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2
$PY -I export_cert.py runs/cert2_k3_d$d.pkl runs/certfile2_k3_d$d.pkl > logs/export2_k3_d$d.log 2>&1
echo chain done for d=$d
