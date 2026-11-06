"""Accurate anchor-relative basis.  For every kept type t at local dimension n (normalisation of build_reduced_blocks):
   Gh_t(n) M_t = Q_t(n) R_t(n)   (M_t = Vb_t N_t, Gh = metric square root),  Ri = R^{-1}/sqrt(sc).
With L_t = n0^{F_t} Ri_t(n0) C_t (C = chol of the analytic centre D_t(n0)):
   W_t L_t   = n0^{F_t} Gh_t(n0)^{-1} Q_t(n0) C_t / sqrt(sc_t(n0))                        (no ill-conditioned products)
   Y_t(n)    = (n/n0)^{2F_t} (sc0/sc_n) C^{-1} P D_t(n) P^T C^{-T},  P = Q(n0)^T Gh(n0) Gh(n)^{-1} Q(n).
"""
import sys, pickle
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np
from polysdp2 import PolyLocal
from exact import ExactLocal

TYPES = pickle.load(open('<ROOT>/dim/runs/exact_types2_k3_d6.pkl', 'rb'))
NREF = pickle.load(open('<ROOT>/dim/runs/red2_k3_d6.pkl', 'rb'))['N']
FTP = pickle.load(open('<ROOT>/dim/uni/ftpoly.pkl', 'rb'))
_aloc = {}


def metric_parts(n, kept):
    """per kept type: (Gh, M, Q, R) at local dimension n."""
    locs = {}
    out = {}
    for ti in kept:
        t = TYPES[ti]
        c = t['cut']
        if c not in locs:
            locs[c] = PolyLocal(c, float(n), scaled=False)
        if c not in _aloc:
            la = ExactLocal(2, 4, c)
            _aloc[c] = [np.array(g, dtype=float) for g in la.G]
        G = np.ones((1, 1))
        for li in t['st']:
            G = np.kron(G, locs[c].G[li])
        G = np.kron(G, _aloc[c][t['ai']])
        w_, V_ = np.linalg.eigh((G + G.T) / 2)
        Gh = (V_ * np.sqrt(np.maximum(w_, 0))) @ V_.T
        Ghi = (V_ / np.sqrt(np.maximum(w_, 1e-300))) @ V_.T
        Vb = np.array(t['Vb'], dtype=float)
        N = np.array(NREF[ti], dtype=float)
        if t['kind'] == 'gram':
            m = Gh.shape[0]
            Z0 = np.zeros((m, m))
            Gh = np.block([[Gh, Z0], [Z0, Gh]]); Ghi = np.block([[Ghi, Z0], [Z0, Ghi]])
            Vb = np.block([[Vb, np.zeros_like(Vb)], [np.zeros_like(Vb), Vb]])
        elif t['kind'] == 'gram2':
            m = Gh.shape[0]
            Z0 = np.zeros((m, m))
            Gh = np.block([[Gh, Z0], [Z0, Gh]]); Ghi = np.block([[Ghi, Z0], [Z0, Ghi]])
            V2 = np.array(t['Vb2'], dtype=float)
            Vb = np.block([[Vb, np.zeros((m, V2.shape[1]))], [np.zeros((m, Vb.shape[1])), V2]])
        M = Vb @ N
        Q, R = np.linalg.qr(Gh @ M)
        out[ti] = dict(Gh=Gh, Ghi=Ghi, M=M, Q=Q, R=R)
    return out


def sc_from_cache(parts, Rinv, kept):
    """align QR signs with the cached normalisation (Ri_cache = R^{-1}/sqrt(sc)) and return the scalars sc.
    QR is unique up to column signs S: Q -> Q S, R -> S R; diag(R^{-1}) = 1/diag(R) fixes S."""
    sc = {}
    for ti, Ri in zip(kept, Rinv):
        p = parts[ti]
        S = np.sign(np.diag(Ri)) * np.sign(np.diag(p['R']))
        p['Q'] = p['Q'] * S[None, :]
        p['R'] = S[:, None] * p['R']
        d = np.diag(Ri) * np.diag(p['R'])          # = 1/sqrt(sc) for every diagonal entry
        sc[ti] = 1.0 / np.median(d) ** 2
    return sc
