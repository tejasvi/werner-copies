#!/bin/bash
# Exact certificate pipeline at k=3, d=$1 WITH the gram2 class.
set -e
D=$1
NZ=${2:-4}
cd <ROOT>/cert
W=runs/exact_k3_d$D
mkdir -p $W
export OMP_NUM_THREADS=8 OPENBLAS_NUM_THREADS=8 MKL_NUM_THREADS=8
P="<ROOT>/venv/bin/python -I"
$P build_exact_types.py 3 $D $W/types_base.pkl
$P exact_zero_modes_k.py 3 $D 1,2,3 $NZ 8 $W/ezm.pkl 1
$P exact_R_par.py 3 $D $W/ezm.pkl $W/R_base.pkl 16
$P exact_R_gram2.py 3 $D $W/ezm.pkl $W/types_g2.pkl $W/R_g2.pkl 16
$P -c "
import pickle
a = pickle.load(open('$W/types_base.pkl','rb')); b = pickle.load(open('$W/types_g2.pkl','rb'))
pickle.dump(a + b, open('$W/types_all.pkl','wb')); print('types', len(a), len(b))
"
$P typed_points_all.py 3 $D $W/types_all.pkl NULLE:runs/big_k3_d$D/meta.pkl $W/Klin.pkl
$P exact_N_all.py $W/types_all.pkl $W/R_base.pkl,$W/R_g2.pkl $W/Klin.pkl $W/N.pkl 32
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 $P build_typed_big.py 3 $D $W/types_all.pkl $W/N.pkl $W 48 8
rm -f $W/ipm.pkl.ckpt
OMP_NUM_THREADS=32 OPENBLAS_NUM_THREADS=32 META=runs/big_k3_d$D/meta.pkl FR_RED=red $P ipm_big.py $W runs/phys_k3_d${D}_fast.pkl $W/ipm.pkl
$P -c "
import pickle, numpy as np
res = pickle.load(open('$W/ipm.pkl','rb')); N = pickle.load(open('$W/N.pkl','rb'))
bl = res['blocks']
out = dict(type_index=[b['type_index'] for b in bl], N=N, D=res['D'],
           Z_exact_basis=[b['Rinv'] @ D @ b['Rinv'].T for b, D in zip(bl, res['D'])])
mins = sorted(np.linalg.eigvalsh(D).min() / np.linalg.eigvalsh(D).max() for D in res['D'])
print('blocks', len(bl), 'smallest rel eig of D:', ['%.1e' % x for x in mins[:5]])
pickle.dump(out, open('$W/res_exact_in.pkl','wb'))
"
$P run_exact.py 3,$D $W/types_all.pkl $W/res_exact_in.pkl $W/cert.pkl 120
$P export_cert4.py $W/cert.pkl $W/certfile4_k3_d$D.pkl
$P verify_cert4.py $W/certfile4_k3_d$D.pkl
