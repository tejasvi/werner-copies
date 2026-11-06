#!/bin/bash
# exact W-basis node certificates (consistency argument): run_exact_poly on the polysdp2 node solutions
cd <ROOT>/dim
for n in "$@"; do
  if [ ! -f runs/certnode_n$n.pkl ]; then
    OMP_NUM_THREADS=2 OPENBLAS_NUM_THREADS=2 <ROOT>/bin/n10 <ROOT>/cert/venv/bin/python -I uni/run_exact_poly.py 3,$n runs/exact_types2_k3_d6.pkl runs/node_n$n.pkl runs/certnode_n$n.pkl 120 > logs/certnode_n$n.log 2>&1
  fi
done
