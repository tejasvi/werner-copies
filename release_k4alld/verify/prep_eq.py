"""Step 2: equality structure and equality multipliers lam.

lam is shipped (certs/lambda_t79_160.npy).  Any lam is admissible: equality rows vanish on every physical tuple, so the
exact check below verifies the residual for whatever lam is used.  With REFIT_LAMBDA=1 the script re-derives lam by the
certificate's own recipe (least squares of the raw s = 0 equality rows against res['EtT_nu'] - mu tr; ~12 min, ~25 GB RAM)
and uses the refit instead (it reproduces the shipped lam to float precision on the reference machine).
Outputs: work/prep_eq.pkl (lam, groups, float site factors), work/prep_eqmats.pkl (raw local matrices).
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))   # python -I does not add the script dir
import common
import os, pickle, time
import numpy as np
from relax import Relaxation, P4, I3

t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
R = Relaxation(4, 5, verbose=False)
orig_dm = R.delete_matrix


def dm_s(slot, order, j):
    """s^j coefficient (j = 0, 1) of the scaled partial trace n^{-1} Tr_slot on S4 words: [p fixes slot] / [p moves slot]"""
    if order is None:
        order = tuple(i for i in range(4) if i != slot)
    Mx = np.zeros((6, 24))
    for a_, p in enumerate(P4):
        if (p[slot] == slot) == (j == 0):
            out = tuple(order.index(p[slot] if p[i] == slot else p[i]) for i in order)
            Mx[I3[out], a_] += 1
    return Mx


s3, a3, la4 = R.loc3['s'], R.loc3['a'], R.loc['a', ()]
EM = dict(S3FT=np.array(s3.FT, dtype=float), A3FT=np.array(a3.FT, dtype=float), LA4FT=np.array(la4.FT, dtype=float))
for slot in (0, 3):
    EM[('embed', slot)] = np.array(R.embed_matrix(slot), dtype=float)
    EM[('dm2', slot, None)] = np.array(orig_dm(2, slot), dtype=float)
for s1, o1 in ((2, (0, 1, 3)), (1, (0, 2, 3)), (1, (3, 0, 2))):
    EM[('dm2', s1, o1)] = np.array(orig_dm(2, s1, o1), dtype=float)
for so in ((0, None), (3, None), (2, (0, 1, 3)), (1, (0, 2, 3)), (1, (3, 0, 2))):
    EM[('dms', so, 0)] = dm_s(so[0], so[1], 0)
    EM[('dms', so, 1)] = dm_s(so[0], so[1], 1)
# groups: Stiefel contrasts at a-slots (X31 slot 0, X22 slot 0, X13 slot 3) and the two marginal pairings
groups, off = [], 0
for f, slot in (('31', 0), ('22', 0), ('13', 3)):
    Ea = EM['LA4FT'] @ (np.eye(24) - 0.5 * EM[('embed', slot)] @ EM[('dm2', slot, None)])
    nrow = 6 ** 4 * Ea.shape[0]
    groups.append([(f, (slot, None), Ea, 1.0, off, nrow)])
    off += nrow
for (f1, s1, o1), (f2, s2, o2) in [(('31', 2, (0, 1, 3)), ('22', 2, (0, 1, 3))), (('22', 1, (0, 2, 3)), ('13', 1, (3, 0, 2)))]:
    E1a = EM['A3FT'] @ EM[('dm2', s1, o1)]
    E2a = EM['A3FT'] @ EM[('dm2', s2, o2)]
    nrow = 6 ** 4 * E1a.shape[0]
    groups.append([(f1, (s1, o1), E1a, 1.0, off, nrow), (f2, (s2, o2), E2a, -1.0, off, nrow)])
    off += nrow
site_eq = {}
for grp in groups:
    for f, so, Ea, sg, o, nrow in grp:
        site_eq[so] = (EM['S3FT'] @ EM[('dms', so, 0)], EM['S3FT'] @ EM[('dms', so, 1)])
lam = np.load(common.P('certs', 'lambda_t79_160.npy'))
assert len(lam) == off, (len(lam), off)
if os.environ.get('REFIT_LAMBDA') == '1':
    res = pickle.load(open(common.P('certs', 'ipm_s0_gp_t79_160.pkl'), 'rb'))
    mm = pickle.load(open(common.P('certs', 'meta_margin_t79_160_slim.pkl'), 'rb'))

    def dm0(nn, slot, order=None):
        return orig_dm(nn, slot, order) if np.isfinite(nn) else dm_s(slot, order, 0)
    R.delete_matrix = dm0
    R.d = float('inf')
    Eraw = R.equality_rows()
    assert Eraw.shape[0] == off
    ey = res['EtT_nu'] - float(res['dobj']) * mm['tr']['31']
    wE, VE = np.linalg.eigh(Eraw.T @ Eraw)
    kp = wE > 1e-10 * wE[-1]
    lam2 = Eraw @ (VE[:, kp] @ ((VE[:, kp].T @ ey) / wE[kp]))
    log('REFIT lam: rank %d, |Eraw^T lam - e_y| %.2e, max |lam_refit - lam_shipped| %.2e' % (
        kp.sum(), np.abs(Eraw.T @ lam2 - ey).max(), np.abs(lam2 - lam).max()))
    lam = lam2
pickle.dump(dict(lam=lam, groups=groups, site_eq=site_eq), open(common.W('prep_eq.pkl'), 'wb'), protocol=4)
pickle.dump(EM, open(common.W('prep_eqmats.pkl'), 'wb'), protocol=4)
log('saved work/prep_eq.pkl and work/prep_eqmats.pkl (%d equality rows, |lam|max %.3e)' % (off, np.abs(lam).max()))
