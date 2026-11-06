"""Build the accurate relative basis at the reference node n0 from the accurate analytic centre acx_n{n0}.pkl:
saves WL_t (float), C_t, Q0, Gh0, sc0, F_t, and Lnum/Lden (exact rounding of L for the record).
Usage: build_rel2.py n0 out.pkl"""
import sys, pickle, math
sys.path.insert(0, '<ROOT>/dim/ac')
import numpy as np
from relbasis import metric_parts, sc_from_cache, TYPES, FTP
n0 = int(sys.argv[1]); outp = sys.argv[2]
ac = pickle.load(open('<ROOT>/dim/runs/acx_n%d.pkl' % n0, 'rb'))
blocks, meta, Rinv = pickle.load(open('<ROOT>/dim/ac/blocks_n%d.pkl' % n0, 'rb'))
kept = list(ac['type_index'])
parts = metric_parts(n0, kept)
sc = sc_from_cache(parts, Rinv, kept)
F = {ti: sum(FTP[TYPES[ti]['cut']]['labels'][li][0] for li in TYPES[ti]['st']) for ti in kept}
WL, C, L = {}, {}, {}
chk = 0.0
for ti, Dm, Ri in zip(kept, ac['D'], Rinv):
    Cm = np.linalg.cholesky((Dm + Dm.T) / 2)
    C[ti] = Cm
    p = parts[ti]
    WL[ti] = float(n0) ** F[ti] * (p['Ghi'] @ p['Q'] @ Cm) / math.sqrt(sc[ti])
    L[ti] = float(n0) ** F[ti] * (Ri @ Cm)
    # consistency: W L computed directly
    chk = max(chk, np.abs(p['M'] @ L[ti] - WL[ti]).max() / np.abs(WL[ti]).max())
print('max relative |M L - WL| = %.2e (direct product vs stable formula)' % chk)
pickle.dump(dict(n0=n0, kept=kept, F=F, WL=WL, C=C, L=L, sc0=sc, Q0={ti: parts[ti]['Q'] for ti in kept},
                 Gh0={ti: parts[ti]['Gh'] for ti in kept}), open(outp, 'wb'), protocol=4)
print('saved', outp)
