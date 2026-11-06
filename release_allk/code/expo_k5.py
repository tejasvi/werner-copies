#!/usr/bin/env python
"""Numerical parts of Proposition 9.3(a) of the paper: the profile LP with an all-d input q_M(TAU) >= 0 (default M = 5,
TAU = 9/20, input (I6)) certifies q_k(t) >= 0 up to t = M TAU (1 - eps)/k for large k, so the constant tends to M TAU = 9/4.
Poisson-mixture certificate (only K_M(1,...,1) rows with compressed sets).  For x = M tau rho, rho = 1 - eps:
    (1 - xS/k)^k = eps + rho (1 - tau S)^M E_k(S),   E_k = exp(sum_{r>=2} bt_r S^r)  (mod S^{k+1}),
    bt_r = (M tau^r - x^r k^{1-r})/r - (x/k)^r sum_{m>=1} (eps^m/m) C(km+r-1, r)      (bt_1 = 0 exactly),
and exp(b S^r) = sum_i e^{-b} b^i/i! (1 + S^r)^i, so E_k is a probability mixture of products of compressed-group factors.
Claim 1: bt_r >= 0 for 2 <= r <= k, all eps in (0, eps0], all k >= K1.  Sufficient: F(r, k) >= 0 with
    F(r, k) = (M - M^r k^{1-r})/r - M^r sum_m (eps0^m/m) C(km+r-1, r)/k^r   (increasing in k);
checked exactly for F(r, K1), 2 <= r <= K1, and F(r, r), K1 < r <= Ran; analytic bound for r > Ran (needs eps0 e^s < 1, s > M).
Claim 2 (truncation; rows exist for |groups| <= k - M):
    q_k(x/k; a) >= eps - Cz z^{-k},   Cz = 2 (1+tau)^M z^{M-1} (1 - tau z)^{-2M} e^{-2M tau z},   1 < z < 1/tau.
Sanity checks: (a) the bt_r formula against a direct series expansion of log E_k; (b) the full certificate at one k.
usage: expo_k5.py eps0 K1 Ran [M tau z]"""
import sys
from fractions import Fraction as Fr
from math import comb
import mpmath as mp

eps0 = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(1, 200)
K1 = int(sys.argv[2]) if len(sys.argv) > 2 else 40
Ran = int(sys.argv[3]) if len(sys.argv) > 3 else 300
MC = int(sys.argv[4]) if len(sys.argv) > 4 else 5
TAU = Fr(sys.argv[5]) if len(sys.argv) > 5 else Fr(9, 20)
ZC = Fr(sys.argv[6]) if len(sys.argv) > 6 else Fr(8, 5)
print('M = %d, tau = %s, M tau = %s, eps0 = %s, K1 = %d, Ran = %d, z = %s' % (MC, TAU, MC * TAU, eps0, K1, Ran, ZC), flush=True)


def msum_upper(r, k, eps):
    """rigorous upper bound for sum_{m>=1} (eps^m/m) C(km+r-1, r)/k^r: exact terms m < Mx, geometric tail with ratio
    <= eps (1 + 1/Mx)^r <= eps * e (Mx >= r)"""
    Mx = max(r, 2)
    tot = Fr(0)
    for m in range(1, Mx):
        tot += eps ** m / m * Fr(comb(k * m + r - 1, r), k ** r)
    tM = eps ** Mx / Mx * Fr(comb(k * Mx + r - 1, r), k ** r)
    q = eps * Fr(2719, 1000)                      # e < 2.719
    assert q < 1
    return tot + tM / (1 - q)


def F_lower(r, k):
    return Fr(MC - Fr(MC ** r, k ** (r - 1)), r) - MC ** r * msum_upper(r, k, eps0)


ok = True
worst = None
for r in range(2, K1 + 1):
    v = F_lower(r, K1)
    if worst is None or v * r < worst[0]:
        worst = (v * r, r, K1)
    ok &= v >= 0
print('(i) F(r, K1 = %d) >= 0 for 2 <= r <= K1: %s; min r*F = %.4f at r = %d' % (K1, ok, float(worst[0]), worst[1]), flush=True)
ok2, worst2 = True, None
for r in range(K1 + 1, Ran + 1):
    v = F_lower(r, r)
    if worst2 is None or v * r < worst2[0]:
        worst2 = (v * r, r)
    ok2 &= v >= 0
print('(ii) F(r, r) >= 0 for K1 < r <= Ran = %d: %s; min r*F = %.4f at r = %d' % (Ran, ok2, float(worst2[0]), worst2[1]) if Ran > K1 else '(ii) empty', flush=True)
# (iii) r > Ran: r F(r, r) >= M - M^r r^{1-r} - r (M/s)^r eps0 e^{2s}/(1 - eps0 e^s); both subtracted terms decrease in r once
# r log(s/M) > 1; interval arithmetic over a grid of s in (M, log(1/eps0)).
mp.iv.dps = 40
best = None
E0 = mp.iv.mpf(eps0.numerator) / eps0.denominator
smax = float(mp.log(mp.mpf(eps0.denominator) / eps0.numerator))
for s_num in range(int(100 * MC) + 1, int(100 * smax)):
    s = mp.iv.mpf(s_num) / 100
    e1 = mp.iv.exp(s)
    if not ((E0 * e1).b < 1):
        continue
    r0 = Ran + 1
    if not ((r0 * mp.iv.log(s / MC)).a > 1):
        continue
    term1 = r0 * (MC / s) ** r0 * E0 * e1 ** 2 / (1 - E0 * e1)
    term2 = mp.iv.mpf(MC) ** r0 * mp.iv.mpf(r0) ** (1 - r0)
    tot = term1 + term2
    if tot.b < MC and (best is None or tot.b < best[1]):
        best = (s_num, float(tot.b))
print('(iii) r > Ran: r F(r, r) >= %d - %s with s = %s/100 -> %s' % (MC, best[1] if best else None, best[0] if best else None, best is not None and best[1] < MC), flush=True)
claim1 = ok and ok2 and best is not None
print('CLAIM 1 (bt_r >= 0 for 2 <= r <= k, all k >= %d, all eps in (0, %s]): %s' % (K1, eps0, claim1), flush=True)

# Claim 2 constant at z
mp.mp.dps = 30
t = mp.mpf(TAU.numerator) / TAU.denominator
z = mp.mpf(ZC.numerator) / ZC.denominator
assert t * z < 1 and z > 1
Cz = 2 * (1 + t) ** MC * z ** (MC - 1) * (1 - t * z) ** (-2 * MC) * mp.exp(-2 * MC * t * z)
print('CLAIM 2: q_k(x/k) >= eps - %.2f * (%s)^(-k); e.g. eps = 1e-3 needs k >= %d, eps = 1e-4 needs k >= %d' % (
    Cz, ZC, int(mp.ceil(mp.log(Cz / mp.mpf('1e-3')) / mp.log(z))), int(mp.ceil(mp.log(Cz / mp.mpf('1e-4')) / mp.log(z)))), flush=True)

# (a) sanity: bt_r formula vs direct series of log E_k (mpmath, 50 digits)
mp.mp.dps = 50
t = mp.mpf(TAU.numerator) / TAU.denominator
def series_check(k, eps, R=25):
    x = MC * t * (1 - eps); rho = 1 - eps
    A = [mp.binomial(k, j) * (-x / k) ** j for j in range(R + 1)]
    A[0] -= eps
    invM = [mp.binomial(r + MC - 1, MC - 1) * t ** r for r in range(R + 1)]
    E = [sum(A[i] * invM[n - i] for i in range(n + 1)) / rho for n in range(R + 1)]
    L = [mp.mpf(0)] * (R + 1)
    for n in range(1, R + 1):
        L[n] = (n * E[n] - sum(i * L[i] * E[n - i] for i in range(1, n))) / n
    err = 0
    for r in range(1, R + 1):
        f = (MC * t ** r - x ** r * mp.mpf(k) ** (1 - r)) / r - (x / k) ** r * mp.nsum(lambda m: eps ** m / m * mp.binomial(k * m + r - 1, r), [1, mp.inf])
        err = max(err, abs(f - L[r]) / max(abs(L[r]), mp.mpf('1e-30')))
    return err, [float(L[r]) for r in range(1, 8)]
for (k, eps) in [(40, mp.mpf('0.005')), (12, mp.mpf('0.003')), (200, mp.mpf('0.004'))]:
    err, Ls = series_check(k, eps)
    print('(a) k = %d eps = %s: max rel. diff formula vs series %.2e; bt_1..7 = %s' % (k, eps, err, ['%.4g' % v for v in Ls]), flush=True)

# (b) sanity: assemble the certificate at one k and compare with q_k (all multisets of parts >= 2, total <= k - M)
def parts_ge2(n, mn=2):
    if n == 0:
        yield ()
        return
    for p in range(mn, n + 1):
        for rest in parts_ge2(n - p, p):
            yield (p,) + rest
def cert_check(k, eps):
    x = MC * t * (1 - eps); rho = 1 - eps
    bt = {r: (MC * t ** r - x ** r * mp.mpf(k) ** (1 - r)) / r - (x / k) ** r * mp.nsum(lambda m: eps ** m / m * mp.binomial(k * m + r - 1, r), [1, mp.inf]) for r in range(2, k + 1)}
    assert all(v >= 0 for v in bt.values())
    tot = [mp.mpf(0)] * (k + 1)
    Z = mp.exp(-sum(bt.values()))
    wsum = 0
    for n in range(0, k - MC + 1):
        for Mset in parts_ge2(n):
            w = Z
            cnt = {}
            for p in Mset:
                cnt[p] = cnt.get(p, 0) + 1
            for p, i in cnt.items():
                w *= bt[p] ** i / mp.factorial(i)
            poly = [mp.mpf(0)] * (k + 1)
            base = [mp.binomial(MC, j) * (-t) ** j for j in range(MC + 1)]
            for j, c in enumerate(base):
                poly[j] = c
            for p in Mset:
                new = poly[:]
                for j in range(k + 1 - p):
                    new[j + p] += poly[j]
                poly = new
            for j in range(k + 1):
                tot[j] += rho * w * poly[j]
            wsum += w
    q = [mp.binomial(k, j) * (-x / k) ** j for j in range(k + 1)]
    rem = [q[j] - tot[j] - (eps if j == 0 else 0) for j in range(k + 1)]
    lb = eps + rem[0] + 2 * sum(min(0, v) for v in rem[1:])
    return float(wsum), float(sum(abs(v) for v in rem)), float(lb)
mp.mp.dps = 30
for (k, eps) in [(30, mp.mpf('0.005')), (40, mp.mpf('0.002'))]:
    ws, rem1, lb = cert_check(k, eps)
    print('(b) k = %d eps = %s: weight of valid rows %.10f | sum |Rem_j| %.3e | certified lower bound for q_k: %.6e (eps = %s) | bound of Claim 2: %.3e' % (
        k, eps, ws, rem1, lb, eps, float(eps - Cz * z ** (-k))), flush=True)
