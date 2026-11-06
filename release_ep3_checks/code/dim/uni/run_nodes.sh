#!/bin/bash
# IPM solves (polysdp2) at a list of node dimensions, sequentially.  Usage: run_nodes.sh n1 n2 ...
PY=<ROOT>/cert/venv/bin/python
cd <ROOT>/dim
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8
for n in "$@"; do
  [ -f runs/node_n$n.pkl ] || LIN_DIM=106 IPM_TOL=5e-8 $PY -I uni/polysdp2.py $n runs/node_n$n.pkl > logs/node_n$n.log 2>&1
done
echo done "$@"
