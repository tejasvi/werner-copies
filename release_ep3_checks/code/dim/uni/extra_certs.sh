#!/bin/bash
# backup certificates at extra integer n (W-basis pipeline works up to n ~ 23-25)
cd <ROOT>/dim
for n in "$@"; do
  [ -f runs/node_n$n.pkl ] || LIN_DIM=106 IPM_TOL=5e-8 OMP_NUM_THREADS=4 OPENBLAS_NUM_THREADS=4 <ROOT>/bin/n10 <ROOT>/cert/venv/bin/python -I uni/polysdp2.py $n runs/node_n$n.pkl > logs/node_n$n.log 2>&1
  [ -f runs/certnode_n$n.pkl ] || OMP_NUM_THREADS=2 <ROOT>/bin/n10 <ROOT>/cert/venv/bin/python -I uni/run_exact_poly.py 3,$n runs/exact_types2_k3_d6.pkl runs/node_n$n.pkl runs/certnode_n$n.pkl ${BITS:-160} > logs/certnode_n$n.log 2>&1
done
