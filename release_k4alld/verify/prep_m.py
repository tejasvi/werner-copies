"""Step 1: multiplier factors M_t from the certificate (float, seconds).

Q_t = M_t M_t^T with M_t = C_t chol(D_t + mu I), C_t = Vb_t Ns_t Rinv_t [Tanc_t], is exactly PSD for ANY real M_t, so the
float construction is part of the certificate's definition, not an approximation that needs error control.
Output: work/prep_blocks.pkl
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))   # python -I does not add the script dir
import common
import pickle, time
import numpy as np
from fractions import Fraction

t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
types = pickle.load(open(common.P('certs', 'exact_types_k4_d4.pkl'), 'rb'))
Ns = pickle.load(open(common.P('certs', 'ns_ident_k4.pkl'), 'rb'))['Ns']
res = pickle.load(open(common.P('certs', 'ipm_s0_gp_t79_160.pkl'), 'rb'))
base = pickle.load(open(common.P('certs', 'meta_base_t79_160_slim.pkl'), 'rb'))
t_ = Fraction(base['t'])
mu = float(res['dobj'])
assert mu > 0
blocks = []
for D, b in zip(res['D'], res['blocks']):
    ti = b['type_index']
    t = types[ti]
    Vb = np.array(t['Vb'], dtype=float)
    if t['kind'] == 'gram':
        Vb = np.block([[Vb, np.zeros_like(Vb)], [np.zeros_like(Vb), Vb]])
    elif t['kind'] == 'gram2':
        V2 = np.array(t['Vb2'], dtype=float)
        m = Vb.shape[0]
        Vb = np.block([[Vb, np.zeros((m, V2.shape[1]))], [np.zeros((m, Vb.shape[1])), V2]])
    C = (Vb @ Ns[ti]) @ b['Rinv']
    if b.get('Nlk') is not None:
        C = C @ b['Nlk']
    if b.get('Tanc') is not None:
        C = C @ b['Tanc']
    Ds = (D + D.T) / 2 + mu * np.eye(D.shape[0])
    L = np.linalg.cholesky(Ds)
    blocks.append(dict(kind=t['kind'], cut=t['cut'], st=tuple(t['st']), ai=t['ai'], f=t.get('f'), n=t['n'], M=C @ L))
log('t = %s, mu = %r, %d multiplier blocks; max |M| %.3e' % (t_, mu, len(blocks), max(np.abs(b['M']).max() for b in blocks)))
pickle.dump(dict(blocks=blocks, t=str(t_), mu=mu), open(common.W('prep_blocks.pkl'), 'wb'), protocol=4)
log('saved work/prep_blocks.pkl')
