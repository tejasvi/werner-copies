"""Rigorous float verification (componentwise error bounds) of the uniform certificate for s = 1/n in [0, h], h = 1/17.

Data: anchor-relative system A(s) = [E(s) | R(s)] (E = selected equality columns / n^3, deg <= 3; R = relative Gram
columns n^{-2F} ..., deg <= 12), objective c(s) (deg <= 12): exact polynomials, known at the 16 nodes s_i = 1/n_i
(ac/rcols_n*.npz: float values + componentwise bounds).  Curve x~(s) = sum_i l_i(s) x~_i (deg 15) through the
rounded analytic centres (Y~_i, lam_i) (float numbers = exact binary rationals).
Claims verified:
  (G) sup_{[0,h]} ||A_R(s) M(s) - I|| <= Gmax < 1, M(s) = sum_i l_i(s) M_i (M_i ~ A_R(s_i)^+, any float matrices):
      G(s) has degree <= 27 -> Lebesgue bound over 28 Chebyshev points.  => A_R(s) has full row rank on [0,h].
  (r) sup ||r_R(s)||, r = c - A x~ (degree <= 27) -> Lebesgue bound over the same 28 points.
  (M) sup ||M(s)||_2 <= Lambda_16 max_i ||M_i||_F.
  => delta(s) = M (A_R M)^{-1} r_R solves A_R delta = r_R with ||delta|| <= Mmax Rmax / (1 - Gmax).
  (P) min over blocks/subintervals of lambda_min of Bernstein coefficients of Y~_t(s) > sqrt(2) ||delta||_max.
Rows outside R and consistency follow from the exact left-kernel argument (lk/exact_tau2.py + certificates).
Usage: uniform_verify.py nodes(comma) [n_eval_points]"""
import sys, pickle, time, math
sys.path.insert(0, '<ROOT>/dim/ac')
import numpy as np
from fractions import Fraction

U = 2.0 ** -53
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
nodes = [int(x) for x in sys.argv[1].split(',')]
ME = int(sys.argv[2]) if len(sys.argv) > 2 else 28
H = Fraction(1, 17)
rel2 = pickle.load(open('<ROOT>/dim/ac/rel2_31.pkl', 'rb'))
rows = np.load('<ROOT>/dim/ac/rowsR.npy')
kept, F = rel2['kept'], rel2['F']
dim = {ti: rel2['L'][ti].shape[0] for ti in kept}
ent = {ti: [(a, b) for a in range(dim[ti]) for b in range(a, dim[ti])] for ti in kept}
off, o = {}, 0
for ti in kept:
    off[ti] = o; o += len(ent[ti])
NY = o
sn = [Fraction(1, n) for n in nodes]


def lagrange_weights(s, pts):
    """exact Lagrange basis values l_j(s) for nodes pts (Fractions)."""
    out = []
    for j, pj in enumerate(pts):
        v = Fraction(1)
        for i, pi in enumerate(pts):
            if i != j:
                v *= (s - pi) / (pj - pi)
        out.append(v)
    return out


def lebesgue(pts, a, b, grid=None):
    """rigorous upper bound of max_{[a,b]} sum_j |l_j(s)|: fine grid + derivative (Markov) bound."""
    m = len(pts)
    grid = grid or 8 * m ** 3
    p = np.array([float(x) for x in pts])
    ss = np.linspace(float(a), float(b), grid)
    lam = np.zeros(grid)
    for j in range(m):
        lj = np.ones(grid)
        for i in range(m):
            if i != j:
                lj *= (ss - p[i]) / (p[j] - p[i])
        lam += np.abs(lj)
    mx = lam.max() * (1 + 1e-10)
    q = (float(b) - float(a)) / (grid - 1) / 2 * m * 2 * (m - 1) ** 2 / (float(b) - float(a))
    assert q < 0.5, q
    return mx / (1 - q)


# ---------------- node data
Ys, lams = [], []
A_nodes, B_nodes, c_nodes = [], [], []
for n in nodes:
    D = np.load('<ROOT>/dim/ac/rcols_n%d.npz' % n)
    E, R, Rb, c = D['E'], D['R'], D['Rbound'], D['c']
    A = np.hstack([E, R])
    Ab = np.hstack([np.abs(E) * U, Rb])
    ac = pickle.load(open('<ROOT>/dim/runs/acx_n%d.pkl' % n, 'rb'))
    y = np.zeros(NY)
    for ti, Z in zip(ac['type_index'], ac['Z_exact_basis']):
        Lt = rel2['L'][ti]
        Zh = Z * float(n) ** (2 * F[ti])
        Y = np.linalg.solve(Lt, np.linalg.solve(Lt, Zh).T).T
        Y = (Y + Y.T) / 2
        y[off[ti]:off[ti] + len(ent[ti])] = [Y[a, b] for (a, b) in ent[ti]]
    lam, *_ = np.linalg.lstsq(E, c - R @ y, rcond=None)
    x = np.concatenate([lam, y])
    log('node %d: float residual |c - A x| = %.3e' % (n, np.linalg.norm(c - A @ x)))
    Ys.append(y); lams.append(lam)
    A_nodes.append(A[rows]); B_nodes.append(Ab[rows]); c_nodes.append(c[rows])
X_nodes = [np.concatenate([l, y]) for l, y in zip(lams, Ys)]
del A, Ab
# ---------------- approximate pseudo-inverses at Chebyshev nodes cm_k (A_R(cm_k) from the exact degree-12 polynomial
# through the integer nodes; M_k are just fixed float matrices -- no accuracy needed)
MM = len(nodes)
cm = [Fraction(math.floor((float(H) / 2) * (1 - math.cos((2 * k + 1) * math.pi / (2 * MM))) * 10 ** 15), 10 ** 15) for k in range(MM)]
M_nodes, Mnorm = [], []
for ck in cm:
    w = np.array([float(x) for x in lagrange_weights(ck, sn)])
    A = sum(w[i] * A_nodes[i] for i in range(len(nodes)))
    Q, Rr = np.linalg.qr(A.T)
    Ri = np.linalg.inv(Rr)
    M_nodes.append(Q @ Ri.T)
    Mnorm.append(np.linalg.norm(Ri) * (1 + 1e-6) + 1e-6 * np.linalg.norm(M_nodes[-1]))
log('pseudo-inverses at %d Chebyshev nodes: max ||M_k||_F %.3e' % (MM, max(Mnorm)))
LamM = lebesgue(cm, 0, H)
Mmax = LamM * max([np.linalg.norm(M) * (1 + 1e-6) for M in M_nodes])
Lam16 = lebesgue(sn, 0, H)
log('Lebesgue(M nodes) %.4f -> Mmax %.3e ; Lebesgue(integer data nodes) %.4f' % (LamM, Mmax, Lam16))
# ---------------- evaluation points
se = [Fraction(math.floor((float(H) / 2) * (1 - math.cos((2 * e + 1) * math.pi / (2 * ME))) * 10 ** 15), 10 ** 15) for e in range(ME)]
Lam_e = lebesgue(se, 0, H)
log('Lebesgue(%d eval points) %.4f' % (ME, Lam_e))
Kc = A_nodes[0].shape[1]
gK = (Kc + 10) * U / (1 - (Kc + 10) * U)
Gs, Rs = [], []
for s in se:
    w = lagrange_weights(s, sn)
    wf = np.array([float(x) for x in w])
    werr = np.abs(wf) * U
    As = sum(wf[i] * A_nodes[i] for i in range(len(nodes)))
    Ab = sum((abs(wf[i]) + werr[i]) * B_nodes[i] + (werr[i] + 20 * U * abs(wf[i])) * np.abs(A_nodes[i]) for i in range(len(nodes)))
    cs = sum(wf[i] * c_nodes[i] for i in range(len(nodes)))
    cb = sum((werr[i] + 20 * U * abs(wf[i])) * np.abs(c_nodes[i]) for i in range(len(nodes)))   # node c exact up to u: folded
    xs = sum(wf[i] * X_nodes[i] for i in range(len(nodes)))
    xb = sum((werr[i] + 20 * U * abs(wf[i])) * np.abs(X_nodes[i]) for i in range(len(nodes)))
    rr = cs - As @ xs
    rb = cb + Ab @ (np.abs(xs) + xb) + np.abs(As) @ xb + gK * (np.abs(As) @ np.abs(xs) + np.abs(cs))
    Rs.append(np.linalg.norm(rr) + np.linalg.norm(rb))
    wm = lagrange_weights(s, cm)
    wmf = np.array([float(x) for x in wm])
    Ms = sum(wmf[k] * M_nodes[k] for k in range(MM))
    Mb = sum((abs(wmf[k]) * U + 20 * U * abs(wmf[k])) * np.abs(M_nodes[k]) for k in range(MM))
    G = As @ Ms - np.eye(As.shape[0])
    Gb = Ab @ (np.abs(Ms) + Mb) + np.abs(As) @ Mb + gK * (np.abs(As) @ np.abs(Ms)) + U * np.eye(As.shape[0])
    g2 = math.sqrt(max(np.linalg.eigvalsh(G.T @ G)[-1], 0) * (1 + 1e-10) + 1e-30) + 1e-12 * np.linalg.norm(G)
    gb2 = math.sqrt(np.abs(Gb).sum(axis=0).max() * np.abs(Gb).sum(axis=1).max())
    Gs.append(g2 + gb2)
    log('s = %.6e (n %.1f): ||r_R|| <= %.3e (float %.3e) ; ||G||_2 <= %.3e' % (float(s), 1 / float(s) if s else float('inf'), Rs[-1], np.linalg.norm(rr), Gs[-1]))
Rmax = Lam_e * max(Rs)
Gmax = Lam_e * max(Gs)
log('Rmax %.3e  Gmax %.3e' % (Rmax, Gmax))
assert Gmax < 1, 'G bound fails'
dmax = Mmax * Rmax / (1 - Gmax)
log('||delta|| <= %.3e ; Y-block operator norm <= sqrt(2) * that = %.3e' % (dmax, math.sqrt(2) * dmax))
pickle.dump(dict(nodes=nodes, se=[str(x) for x in se], cm=[str(x) for x in cm], Rs=Rs, Gs=Gs, Lam16=Lam16, LamM=LamM, Lam_e=Lam_e, Mmax=Mmax, Rmax=Rmax,
                 Gmax=Gmax, dmax=dmax), open('<ROOT>/dim/ac/uniform_part1.pkl', 'wb'))
# ---------------- PSD of Y~_t(s) via Bernstein coefficients on subintervals
from math import comb
NSUB = 16
deg = len(nodes) - 1
worst = np.inf
for j in range(NSUB):
    a, b = H * j / NSUB, H * (j + 1) / NSUB
    # Bernstein coefficients of the interpolant: values at Chebyshev-free approach: power basis in t on [a,b]
    # l_i(a + (b-a) t) = sum_k p_ik t^k (exact) -> Bernstein: beta_ik = sum_{m<=k} C(k,m)/C(deg,m) p_im
    P = []
    for i in range(len(nodes)):
        poly = [Fraction(1)]
        den = Fraction(1)
        for q in range(len(nodes)):
            if q == i:
                continue
            # factor (a + (b-a)t - s_q) / (s_i - s_q)
            c0 = (a - sn[q]); c1 = (b - a)
            new = [Fraction(0)] * (len(poly) + 1)
            for kk, v in enumerate(poly):
                new[kk] += v * c0
                new[kk + 1] += v * c1
            poly = new
            den *= (sn[i] - sn[q])
        P.append([v / den for v in poly])
    beta = np.array([[float(sum(Fraction(comb(k, m), comb(deg, m)) * P[i][m] for m in range(k + 1))) for k in range(deg + 1)] for i in range(len(nodes))])
    for ti in kept:
        sl = slice(off[ti], off[ti] + len(ent[ti]))
        for kk in range(deg + 1):
            v = sum(beta[i, kk] * Ys[i][sl] for i in range(len(nodes)))
            vb = sum(abs(beta[i, kk]) * np.abs(Ys[i][sl]) for i in range(len(nodes))) * 40 * U
            Bm = np.zeros((dim[ti], dim[ti])); Bb = np.zeros((dim[ti], dim[ti]))
            for e_, (p_, q_) in enumerate(ent[ti]):
                Bm[p_, q_] = Bm[q_, p_] = v[e_]
                Bb[p_, q_] = Bb[q_, p_] = vb[e_]
            lmin = np.linalg.eigvalsh(Bm)[0] - np.linalg.norm(Bb) - 10 * dim[ti] ** 2 * U * np.abs(Bm).max()
            worst = min(worst, lmin)
    log('subinterval %d/%d: worst lambda_min so far %.4f' % (j + 1, NSUB, worst))
log('PSD margin %.4f vs correction bound %.3e : %s' % (worst, math.sqrt(2) * dmax, 'UNIFORM CERTIFICATE VERIFIED' if worst > math.sqrt(2) * dmax else 'FAIL'))
