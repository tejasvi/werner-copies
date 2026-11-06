"""Absolute shadows of the word-level residual (own implementation, factorised; no per-word evaluation needed).

For a term  sum_w (core . (x)_l P_l(s)[:, w_l] (x) P_a[:, w_a])  the triangle inequality gives
    sum_w |[s^j] term(w)|  <=  sum_{rows} |core| * prod_l (sum_{w_l} |.|) (x) (sum_{w_a} |.|),
with, per site, the s^0 data (B0), exactly one site carrying s^1 data (B1), or the sum over ALL orders of |coef|
(S2 majorant: sum_w sum_{j>=2} |[s^j] rho(w)| <= full shadow).  For blocks |Q_ij| <= (|Mi| |Mi|^T)_ij 2^-2E.
Outputs (float64, nonnegative terms only, then x (1 + 1e-9)):
    B0 >= sum_f sum_w |R0_f(w)|  >= max_o |R0(o)|,  B1 likewise for R1  (uniform CRT magnitude bounds, times Den);
    S2 >= sum_f sum_w sum_{j>=2} |[s^j] rho_f(w)|  >= sum_o |sum_{w in o} r2(w; s)| / s^2  for 0 < s <= 1.
Usage: shadow_words.py out.pkl
"""
import os, sys, time, pickle, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import k5defs as KD

t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
K = KD.K
cert = KD.load_cert()
FTP = KD.load_ftp()
E = KD.m_exponent(cert)
keys = KD.block_keys(cert)
parts, Elam, diag = KD.equality_parts(cert)
B0 = {f: 0.0 for f in KD.FAMS}; B1 = {f: 0.0 for f in KD.FAMS}; S2 = {f: 0.0 for f in KD.FAMS}

SITE = {}


def site_sums(cut, li):
    """row sums over words of |C_0|, |C_1|, sum_j |C_j| for the label's polynomial data"""
    if (cut, li) not in SITE:
        C = KD.site_poly(FTP, cut, li)
        a = np.abs(C[0]).sum(axis=1).astype(np.float64)
        b = np.abs(C[1]).sum(axis=1).astype(np.float64) if len(C) > 1 else np.zeros_like(a)
        full = sum(np.abs(Cj) for Cj in C).sum(axis=1).astype(np.float64)
        SITE[cut, li] = (a, b, full)
    return SITE[cut, li]


def kron_all(vs):
    out = np.ones(1)
    for v in vs:
        out = np.multiply.outer(out, v).reshape(-1)
    return out


def raw_pair_layout(vec_pairs, dims):
    """vectors over pair indices (i_l, j_l) (length d_l^2 each, i major) -> matrix over raw (rows, cols) = ((i_0..i_5), (j_0..j_5))"""
    T = kron_all(vec_pairs).reshape(sum([[d, d] for d in dims], []))
    L = len(dims)
    order = [2 * i for i in range(L)] + [2 * i + 1 for i in range(L)]
    n = int(np.prod(dims))
    return T.transpose(order).reshape(n, n)


for ik, (key, lst) in enumerate(keys.items()):
    cut, st, ai, f = key
    dims = KD.key_dims(FTP, key)
    n = int(np.prod(dims))
    absQ = np.zeros((n, n))
    for bi in lst:
        Mi = np.abs(KD.rounded_M(cert['blocks'][bi], E).astype(np.float64))
        absQ += Mi @ Mi.T
    absQ *= 2.0 ** (-2 * E)
    _, adims, off, FT = KD.anc_ft(cut)
    anc = np.abs(FT[off[ai]:off[ai + 1]]).sum(axis=1).astype(np.float64)
    ss = [site_sums(cut, li) for li in st]
    B0[f] += float(np.sum(absQ * raw_pair_layout([s[0] for s in ss] + [anc], dims)))
    for l in range(K):
        if np.any(ss[l][1]):
            B1[f] += float(np.sum(absQ * raw_pair_layout([ss[m][1] if m == l else ss[m][0] for m in range(K)] + [anc], dims)))
    S2[f] += float(np.sum(absQ * raw_pair_layout([s[2] for s in ss] + [anc], dims)))
    if ik % 1000 == 0:
        log('key %d/%d' % (ik, len(keys)))

z, y, za, zat = KD.obj_trace_factors()
for zz, zx, w in ((z, za, 1.0 / (16 * KD.T_Q.denominator ** K)), (y, zat, float(KD.NU_Q) / 16)):
    a0 = float(np.abs(zz[0]).sum()); a1 = float(np.abs(zz[1]).sum()); af = float(sum(np.abs(v).sum() for v in zz))
    ax = float(np.abs(zx).sum())
    B0['31'] += w * a0 ** K * ax
    B1['31'] += w * K * a1 * a0 ** (K - 1) * ax
    S2['31'] += w * af ** K * ax
for e in parts:
    d0 = np.abs(KD.delete_site(e['slot'], e['order'], 0)).sum(axis=1).astype(np.float64)
    d1 = np.abs(KD.delete_site(e['slot'], e['order'], 1)).sum(axis=1).astype(np.float64)
    am = np.abs(e['Amap']).sum(axis=1).astype(np.float64)
    core = np.abs(e['mui']).astype(np.float64).reshape(-1) * 2.0 ** (-Elam) / e['aden']
    B0[e['f']] += float(core @ kron_all([d0] * K + [am]))
    B1[e['f']] += float(sum(core @ kron_all([d1 if m == l else d0 for m in range(K)] + [am]) for l in range(K)))
    S2[e['f']] += float(core @ kron_all([d0 + d1] * K + [am]))
SAFE = 1 + 1e-9
out = dict(B0={f: B0[f] * SAFE for f in KD.FAMS}, B1={f: B1[f] * SAFE for f in KD.FAMS}, S2f={f: S2[f] * SAFE for f in KD.FAMS},
           S2=sum(S2.values()) * SAFE, E=E, Elam=Elam, eq_diag=diag)
pickle.dump(out, open(sys.argv[1], 'wb'), protocol=4)
log('B0 %s' % {f: '%.4e' % v for f, v in out['B0'].items()})
log('B1 %s' % {f: '%.4e' % v for f, v in out['B1'].items()})
log('S2 majorant (full absolute shadow, all orders, x(1+1e-9)) = %.6e  per family %s' % (out['S2'], {f: '%.3e' % v for f, v in out['S2f'].items()}))
log('equality literal-row fit |mu Gx - phi|/|phi| max: %.3e' % max(d[3] / max(d[4], 1e-300) for d in diag))
