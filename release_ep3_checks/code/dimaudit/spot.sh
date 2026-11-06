#!/bin/bash
# Spot-checks: strict PD (Sylvester) on node certificates + export & literal verification of two node certificates.
PY=<ROOT>/cert/venv/bin/python
D=<ROOT>/dim
cd <ROOT>/dimaudit
$PY -I $D/uni/pd_check.py $D/runs/certnode_n22.pkl $D/runs/certnode_n24.pkl $D/runs/certnode_n25.pkl $D/runs/certnode_n26.pkl $D/runs/certnode_n27.pkl $D/runs/certnode_n28.pkl > logs/pd_new.log 2>&1 &
for n in 17 23; do
  ( $PY -I $D/export_cert.py $D/runs/certnode_n$n.pkl runs/certfile_node_n$n.pkl > logs/export_n$n.log 2>&1 && \
    sha256sum runs/certfile_node_n$n.pkl >> logs/export_n$n.log && \
    $PY -I $D/verify_cert.py runs/certfile_node_n$n.pkl > logs/verify_node_n$n.log 2>&1 ) &
done
wait
