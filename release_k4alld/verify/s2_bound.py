"""Rigorous upper bound for S2 = sum_w B2(w): the full absolute shadow sum_w |rho|_shadow(w) (all s-degrees, no
subtraction), computed with nonnegative float sums and inflated by 1.01 (float relative error here is < 1e-8).
For 0 <= s <= 1 every s-degree >= 2 part of rho(w; s) is bounded by s^2 times its absolute coefficient sum, which this
shadow dominates."""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))   # python -I does not add the script dir
import common
import os, sys, pickle
import numpy as np
from relax import P4, SWAP03, FAMILIES
from local import compose, ncycles
from exact import ExactLocal
FTP = common.load_ftp()

PB = pickle.load(open(common.W('prep_blocks.pkl'), 'rb'))
blocks = PB['blocks']
tot_blk = 0.0
cache_anc = {}
for b in blocks:
    M = np.abs(b['M']) + 2.0 ** -60          # dominates |M'| (fixed-point rounding to 2^-60)
    nraw = b['n']
    if b['kind'] == 'src':
        parts = [(M, M, 1.0)]
    else:
        parts = [(M[:nraw], M[:nraw], 1.0), (M[nraw:], M[nraw:], 1.0), (M[:nraw], M[nraw:], 2.0)]
    coef, off, labels = FTP[b['cut']]['coef'], FTP[b['cut']]['off'], FTP[b['cut']]['labels']
    vs = []
    for li in b['st']:
        f = labels[li][0]
        rows = slice(off[li], off[li + 1])
        s = np.zeros(off[li + 1] - off[li])
        for j in range(2 * f + 1):
            s += np.abs(np.array(coef[2 * f - j, rows], dtype=float)).sum(axis=1)
        vs.append(s)
    c = b['cut']
    if c not in cache_anc:
        la = ExactLocal(2, 4, c)
        cache_anc[c] = (np.abs(np.array(la.FT, dtype=float)), la.off)
    FTa, offa = cache_anc[c]
    va = FTa[offa[b['ai']]:offa[b['ai'] + 1]].sum(axis=1)
    vecs = vs + [va]
    dims = [int(round(np.sqrt(len(v)))) for v in vecs]
    for X, Y, w in parts:
        Qb = w * (X @ Y.T)                          # nonnegative, dominates |X' Y'^T| entrywise
        T = Qb.reshape(dims + dims)
        order = []
        for i in range(5):
            order += [i, 5 + i]
        T = T.transpose(order).reshape([d * d for d in dims])
        for v in vecs:
            T = np.tensordot(T, v, axes=([0], [0]))
        tot_blk += float(T)
nc = np.array([ncycles(q) for q in P4]); ncs = np.array([ncycles(compose(SWAP03, q)) for q in P4])
t = 79 / 160
zsum = sum(np.abs((nc == 4 - j) - t * (ncs == 4 - j)).sum() for j in range(4))
ysum = sum(((nc == 4 - j)).sum() for j in range(4))
tot_obj = (1 / 16) * zsum ** 4 * np.sum(2.0 ** ncs) + (1e-4 / 16) * ysum ** 4 * np.sum(2.0 ** nc)
PE = pickle.load(open(common.W('prep_eq.pkl'), 'rb'))
tot_eq = 0.0
for grp in PE['groups']:
    for f, so, Ea, sg, o, nrow in grp:
        import importlib
        lam = np.abs(PE['lam'][o:o + nrow]) + 2.0 ** -60
        a_eq, b_eq = PE['site_eq'][so]
        v = (np.abs(a_eq) + np.abs(b_eq)).sum(axis=1) * (1 + 1e-6)
        ve = np.abs(Ea).sum(axis=1) * (1 + 1e-6)
        T = lam.reshape((6,) * 4 + (Ea.shape[0],))
        for vv in (v, v, v, v, ve):
            T = np.tensordot(T, vv, axes=([0], [0]))
        tot_eq += float(T)
S2u = 1.01 * (tot_blk + tot_obj + tot_eq)
print('shadow totals: blocks %.4e, objective/trace %.4e, equality %.4e; S2 upper bound %.4e' % (tot_blk, tot_obj, tot_eq, S2u))
pickle.dump(dict(S2_upper=S2u, blk=tot_blk, obj=tot_obj, eq=tot_eq), open(common.W('s2_bound.pkl'), 'wb'))
