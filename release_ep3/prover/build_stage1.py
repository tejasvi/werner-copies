"""Prover side, stage 1: the route-A min-norm correction delta(tau_c) = B_c (A_R(tau_c) B_c)^{-1} r_R(tau_c) at the
q+1 Chebyshev-Lobatto nodes, and its degree-q Bernstein coefficients on [0, 1/9] (conditioned, s-scaled
coordinates of every column).  Output: npz with beta (q+1 x ncol), delta nodes, tau.
Usage: build_stage1.py coldir neumann.pkl residual.pkl out.npz"""
import math, pickle, sys, time
from fractions import Fraction
import numpy as np
coldir, nmp, resp, outp = sys.argv[1:5]
t0 = time.time(); log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
meta = pickle.load(open(coldir + '/meta.pkl', 'rb'))
NM = pickle.load(open(nmp, 'rb'))
RS = pickle.load(open(resp, 'rb'))
k, nrow, ncol = meta['k'], meta['nrow'], meta['ncol']
R = np.array(NM['rows']); rho = len(R); q = NM['q']
D0 = 9; smax = 1.0 / D0
A = np.load(nmp + '.A.npy', mmap_mode='r'); Bs = np.load(nmp + '.BR.npy', mmap_mode='r')
nq = A.shape[0]
sig = [Fraction(round((1 - math.cos(math.pi * c / (nq - 1))) / (2 * D0) * 10 ** 9), 10 ** 9) for c in range(nq)]
AR = np.array([A[c][R] for c in range(nq)])
log('A_R at %d sigma nodes loaded' % nq)
Dv = RS['Dver']; sq = [Fraction(1, d) for d in Dv]
rq = [[Fraction(x) for x in RS['rfull'][d]] for d in Dv]
def lag(nodes, t):
    w = []
    for i, x in enumerate(nodes):
        v = Fraction(1)
        for j, y in enumerate(nodes):
            if j != i: v *= (t - y) / (x - y)
        w.append(v)
    return w
tau = (np.cos(np.pi * np.arange(q + 1) / q)[::-1] + 1) / 2 * smax
dl = np.zeros((q + 1, ncol))
for c in range(q + 1):
    ws = np.array([float(x) for x in lag(sig, Fraction(float(tau[c])))])
    Ac = np.tensordot(ws, AR, axes=1)
    wr = lag(sq, Fraction(float(tau[c])))
    rr = np.array([float(sum(wr[i] * rq[i][j] for i in range(len(Dv)))) for j in R])
    Bc = np.asarray(Bs[c])
    y = np.linalg.solve(Ac @ Bc, rr)
    dl[c] = Bc @ y
    log('  node %d (tau %.5f): ||r_R|| %.3e, max|delta| %.3e' % (c, tau[c], np.linalg.norm(rr), np.abs(dl[c]).max()))
u = tau / smax
M = np.array([[math.comb(q, j) * u[c] ** j * (1 - u[c]) ** (q - j) for j in range(q + 1)] for c in range(q + 1)])
beta = np.linalg.solve(M, dl)
log('Bernstein coefficients: cond(M) %.2e, max |beta| %.3e (block %.3e, eq %.3e)' % (
    np.linalg.cond(M), np.abs(beta).max(), np.abs(beta[:, [c for c, x in enumerate(meta['cmeta']) if x[0] == 'blk']]).max(),
    np.abs(beta[:, [c for c, x in enumerate(meta['cmeta']) if x[0] == 'eq']]).max()))
np.savez(outp, beta=beta, delta=dl, tau=tau, q=q)
log('written %s' % outp)
