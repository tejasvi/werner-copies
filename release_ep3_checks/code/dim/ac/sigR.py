"""Row-selected full-column system A_R(s) (anchor-relative, equality columns scaled n^-3 and unit-normalised at n_ref):
smallest singular value across n, and ||A_R(n1) - A_R(n0)|| / |s1 - s0| for neighbouring n.
Usage: sigR.py n_ref n1 n2 ..."""
import sys, pickle, time
sys.path.insert(0, '<ROOT>/dim/ac')
import numpy as np
import scipy.linalg as sla
from relsys import RelSys
t0 = time.time()
rel = pickle.load(open('<ROOT>/dim/ac/rel31.pkl', 'rb'))
RS = RelSys(rel)
ns = [int(x) for x in sys.argv[1:]]
nref = ns[0]
R0, E0, c0 = RS.system(nref)
E0 = E0 / float(nref) ** 3
en = np.linalg.norm(E0, axis=0)
A0 = np.hstack([E0 / en, R0])
Q, Rr, piv = sla.qr(A0.T, mode='economic', pivoting=True)
rows = np.sort(piv[:2634])
np.save('<ROOT>/dim/ac/rowsR.npy', rows)
print('row selection done %.0fs' % (time.time() - t0), flush=True)
prev = None
for n in ns:
    if n == nref:
        A = A0
    else:
        R, E, c = RS.system(n)
        A = np.hstack([E / float(n) ** 3 / en, R])
    AR = A[rows]
    w = np.linalg.eigvalsh(AR @ AR.T)
    line = 'n=%6d: sigma_min(A_R) %.3e sigma_max %.3e' % (n, np.sqrt(max(w[0], 0)), np.sqrt(w[-1]))
    if prev is not None:
        pn, pA = prev
        dA = np.linalg.norm(AR - pA, 2) / abs(1.0 / n - 1.0 / pn)
        line += '  | ||dA_R/ds|| (vs n=%d) %.3e' % (pn, dA)
    print(line + '  %.0fs' % (time.time() - t0), flush=True)
    prev = (n, AR)
