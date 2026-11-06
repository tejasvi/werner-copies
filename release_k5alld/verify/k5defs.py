"""k5alldaudit: shared definitions for the independent exact all-d check of the k = 5, t = 9/20 certificate.

Own implementation (auditor).  It uses from the producer only the certificate data (r49_cert.pkl), the per-site
polynomial data (uni/ftpoly.pkl) and local.module_data (the ancilla's irreducible module data, n = 2), which together
define the certificate's raw basis.  Word-level conventions:
  * a word is w = (w_0, .., w_4, w_a) in S_4^5 x S_4, letters indexed by P4 = itertools.permutations(range(4))
    (lexicographic; p[i] = image of i; compose(p, q)[i] = p[q[i]], V_p V_q = V_{compose(p, q)});
  * a family-f moment tuple is X_f = sum_w x_f(w) V_{w_0} (x) .. (x) V_{w_4} (x) V_{w_a};
  * the residual of the certificate is the linear functional rho = c - nu tau - sum_b <Q_b, M_b(.)> - lam.E(.),
    rho(x) = sum_f sum_w rho_f(w; s) x_f(w), every rho_f(w; s) a polynomial in s = 1/n.
"""
import os, sys, pickle, itertools, math
from fractions import Fraction
import numpy as np

K = 5
NW = 24
NWORD = NW ** (K + 1)
HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.environ.get('K5_CERT', os.path.join(os.path.dirname(HERE), 'certs', 'k5_cert_t9_20.pkl'))
FTPF = os.environ.get('K5_FTP', os.path.join(os.path.dirname(HERE), 'data', 'ftpoly.pkl'))
ZM = os.environ.get('K5_ZM', os.path.join(os.path.dirname(HERE), 'zm'))      # local.py (module_data)

P4 = tuple(itertools.permutations(range(4)))
I4 = {p: i for i, p in enumerate(P4)}
P3 = tuple(itertools.permutations(range(3)))
I3 = {p: i for i, p in enumerate(P3)}


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def ncycles(p):
    seen, c = set(), 0
    for i in range(len(p)):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = p[j]
    return c


SWAP03 = (3, 1, 2, 0)
FAMS = ('31', '22', '13')
GF = {'31': [p + (3,) for p in P3], '13': [p + (3,) for p in P3],
      '22': [(0, 1, 2, 3), (1, 0, 2, 3), (0, 1, 3, 2), (1, 0, 3, 2)]}
TRANSP = {f: [g for g in GF[f] if sum(g[i] != i for i in range(4)) == 2] for f in FAMS}
LMUL = {g: np.array([I4[compose(g, p)] for p in P4], dtype=np.int64) for f in FAMS for g in GF[f]}
RMUL = {g: np.array([I4[compose(p, g)] for p in P4], dtype=np.int64) for f in FAMS for g in GF[f]}
INV = np.array([I4[inverse(p)] for p in P4], dtype=np.int64)

T_Q = Fraction(9, 20)
NU_Q = Fraction(1, 1000)


def load_cert():
    c = pickle.load(open(CERT, 'rb'))
    assert c['k'] == K and Fraction(c['t']) == T_Q and Fraction(c['nu']) == NU_Q, (c['k'], c['t'], c['nu'])
    return c


def load_ftp():
    return pickle.load(open(FTPF, 'rb'))


# ---------------- per-site data: P_l(s) = sum_j coef[2f - j] s^j on the rows of label li ----------------
def site_poly(FTP, cut, li):
    """integer matrices C_j (d^2 x 24), j = 0..2f, with P(s) = sum_j C_j s^j; checks degree <= 2f and integrality"""
    P = FTP[cut]
    coef = np.asarray(P['coef'], dtype=object)
    f = P['labels'][li][0]
    rows = slice(P['off'][li], P['off'][li + 1])
    blk = coef[:, rows, :]
    for i in range(blk.shape[0]):
        if i > 2 * f:
            assert all(int(x) == 0 for x in blk[i].ravel()), ('degree > 2f', cut, li, i)
    out = []
    for j in range(2 * f + 1):
        Cj = np.array([[int(x) for x in row] for row in blk[2 * f - j]], dtype=np.int64)
        assert np.all(Cj == np.array(blk[2 * f - j], dtype=object).astype(float)), 'non-integer site coefficient'
        out.append(Cj)
    return out


# ---------------- ancilla data (n = 2, 4 replicas): rows of G_nu pi_nu(p), the certificate's ExactLocal(2, 4, cut).FT ----------
_ANC = {}


def anc_ft(cut):
    cut = tuple(sorted(cut))
    if cut in _ANC:
        return _ANC[cut]
    if ZM not in sys.path:
        sys.path.insert(0, ZM)
    from local import module_data, perms
    assert tuple(perms(4)) == P4
    data = module_data(4, cut, 2)
    labels = list(data)
    dims = [data[l]['dim'] for l in labels]
    off = [0]
    for d in dims:
        off.append(off[-1] + d * d)
    FT = np.zeros((off[-1], 24), dtype=np.int64)
    for li, l in enumerate(labels):
        G = data[l]['G']
        for a, pi in enumerate(data[l]['pi']):
            Mx = G * pi
            for i in range(dims[li]):
                for j in range(dims[li]):
                    v = Mx[i, j]
                    assert v.is_integer
                    FT[off[li] + i * dims[li] + j, a] = int(v)
    _ANC[cut] = (labels, dims, off, FT)
    return _ANC[cut]


# ---------------- blocks: keys (cut, st, ai, f) and exact rounding ----------------
def block_keys(cert):
    keys = {}
    for bi, b in enumerate(cert['blocks']):
        assert b['kind'] == 'src'
        keys.setdefault((tuple(b['cut']), tuple(b['st']), int(b['ai']), b['f']), []).append(bi)
    return keys


def key_dims(FTP, key):
    cut, st, ai, f = key
    _, adims, _, _ = anc_ft(cut)
    return [FTP[cut]['dims'][li] for li in st] + [adims[ai]]


def m_exponent(cert):
    mmax = max(float(np.abs(b['M']).max()) for b in cert['blocks'])
    return 62 - int(math.floor(math.log2(mmax)))


def rounded_M(b, E):
    """integer factor Mi with M ~ Mi 2^-E (|Mi| < 2^63); Q = Mi Mi^T 2^-2E is exactly PSD"""
    X = np.rint(np.asarray(b['M'], dtype=np.float64) * 2.0 ** E)
    assert np.abs(X).max() < 2.0 ** 63
    return X.astype(np.int64)


# ---------------- objective and trace (family 31): site and ancilla factors ----------------
def obj_trace_factors():
    """objective: (1/16) prod_l n^-4 (n^nc - t n^nc(S.)) * 2^nc(S.)  ->  integer site vectors z_j = 20 [nc = 4-j] - 9 [ncs = 4-j]
    (value z_j / 20 at order s^j), ancilla za = 2^ncs;  trace: (1/16) prod_l n^(nc-4) 2^nc -> y_j = [nc = 4-j], zat = 2^nc."""
    nc = np.array([ncycles(p) for p in P4])
    ncs = np.array([ncycles(compose(SWAP03, p)) for p in P4])
    z = [(T_Q.denominator * (nc == 4 - j) - T_Q.numerator * (ncs == 4 - j)).astype(np.int64) for j in range(4)]
    y = [(nc == 4 - j).astype(np.int64) for j in range(4)]
    za = (2 ** ncs).astype(np.int64)
    zat = (2 ** nc).astype(np.int64)
    return z, y, za, zat


# ---------------- equalities ----------------
def delete_site(slot, order, j):
    """(6 x 24) 0/1 matrix: coefficient of s^j in n^-1 Tr_slot V_p = [p fixes slot] V_p' + s [p moves slot] V_p'
    (survivors relabelled: new position i <-> old slot order[i])"""
    if order is None:
        order = tuple(i for i in range(4) if i != slot)
    M = np.zeros((6, 24), dtype=np.int64)
    for a, p in enumerate(P4):
        fixed = (p[slot] == slot)
        if fixed == (j == 0):
            pp = {i: (p[slot] if p[i] == slot else p[i]) for i in range(4) if i != slot}
            out = tuple(order.index(pp[order[i]]) for i in range(3))
            M[I3[out], a] += 1
    return M


def delete_anc(slot, order=None):
    """(6 x 24) integer matrix of Tr_slot on (C^2)^{x4}: V_p -> 2^[p fixes slot] V_p'"""
    return 2 * delete_site(slot, order, 0) + delete_site(slot, order, 1)


def embed_anc(slot):
    """(24 x 6): V_q (3 replicas) -> V_q (x) I at slot (survivors in natural order)"""
    order = tuple(i for i in range(4) if i != slot)
    M = np.zeros((24, 6), dtype=np.int64)
    for a, q in enumerate(P3):
        p = [None] * 4
        p[slot] = slot
        for i_new, i_old in enumerate(order):
            p[i_old] = order[q[i_new]]
        M[I4[tuple(p)], a] = 1
    return M


def gram(perms_, n):
    return np.array([[n ** ncycles(compose(inverse(v), w)) for w in perms_] for v in perms_], dtype=np.int64)


def exact_pinv(G):
    import sympy as sp
    Gp = sp.Matrix(G.tolist()).pinv()
    return Gp, np.array([[float(x) for x in row] for row in Gp.tolist()])


def equality_parts(cert, MBITS=62):
    """Own derivation of the exact equality functional from the certificate's compressed multipliers.
    Row (u, beta) of a part (f, slot, order) is  sum_w x_f(w) prod_l (s3FT . D_slot)[u_l, w_l] (FTa . Aop)[beta, w_a].
    Site multipliers are folded onto S3 words (independent operators for n >= 3: any functional is admissible); the
    ancilla functional phi = L'.FTa is re-expressed on LITERAL trace rows Gx.Aop (mu = phi Gx^+), which vanish on every
    physical tuple, then mu is rounded to 2^-Elam.  Returns (parts, Elam, diagnostics)."""
    s3FT = np.asarray(cert['s3FT'], dtype=np.float64)
    reps = np.asarray(cert['reps'])
    Ga = gram(P4, 2)
    Ga3 = gram(P3, 2)
    _, Gap = exact_pinv(Ga)
    _, Ga3p = exact_pinv(Ga3)
    parts, diag = [], []
    for g in cert['groups']:
        lam = np.asarray(g['lam'], dtype=np.float64)
        na = lam.shape[1]
        L = np.zeros((6,) * K + (na,))
        for r, row in zip(reps, lam):
            L[tuple(int(x) for x in r)] += row
        Lp = np.einsum('abcdez,aA,bB,cC,dD,eE->ABCDEz', L, s3FT, s3FT, s3FT, s3FT, s3FT, optimize=True)
        for (f, slot, order, sg) in g['parts']:
            if g['kind'] == 'stiefel':
                FTa = np.asarray(cert['laFT'], dtype=np.float64)
                Gx, Gxp, aden = Ga, Gap, 2
                Aop = 2 * np.eye(24, dtype=np.int64) - embed_anc(slot) @ delete_anc(slot)
            else:
                FTa = np.asarray(cert['a3FT'], dtype=np.float64)
                Gx, Gxp, aden = Ga3, Ga3p, 1
                Aop = delete_anc(slot, order)
            phi = Lp @ FTa
            mu = phi @ Gxp
            diag.append((g['kind'], f, slot, float(np.abs(mu @ Gx - phi).max()), float(np.abs(phi).max())))
            parts.append(dict(kind=g['kind'], f=f, slot=slot, order=order, sg=int(sg), mu=mu, Amap=Gx @ Aop, aden=aden))
    mumax = max(float(np.abs(e['mu']).max()) for e in parts)
    Elam = MBITS - int(math.floor(math.log2(mumax)))
    for e in parts:
        X = np.rint(e['mu'] * 2.0 ** Elam)
        assert np.abs(X).max() < 2.0 ** 63
        e['mui'] = X.astype(np.int64)
    return parts, Elam, diag


def common_den(E, Elam):
    """Den: every residual coefficient is an integer multiple of 1/Den."""
    return math.lcm(2 ** (2 * E), 2 ** Elam * 2, T_Q.denominator ** K * 16, NU_Q.denominator * 16)
