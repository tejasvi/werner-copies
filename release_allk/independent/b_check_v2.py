#!/usr/bin/env python3
"""Independent checks for Proposition 9.3(a) of the paper (own code).
(M, tau) = (5, 9/20), rho = 1 - eps, x = 5 tau rho.
P1  bt_r formula vs the exact rational series of log E_k, E_k = [(1 - xS/k)^k - eps](1 - tau S)^{-5}/rho.
P2  Claim 1, exact rational LOWER bounds of F(r,40) (2 <= r <= 40) and F(r,r) (40 < r <= 300), eps0 = 1/200;
    m-sum exact up to M = max(r, 60), tail <= term_M rho_M/(1 - rho_M), rho_M = eps0 (1 + 1/M)^r.
P3  Claim 1 for r > 300 (interval arithmetic): r F(r,r) >= 5 - r(5/r)^r - r (5/s)^r e^s (-log(1 - eps0 e^s)).
P4  Claim 2 constant Cz = 2 (1 + tau)^5 z^4 (1 - tau z)^{-10} exp(-10 tau z) at z = 8/5 (interval arithmetic).
P5  K(eps), K*(eps), K**(eps) examples, and a brute-force check of the level-by-level interval argument of an earlier
    version of the proof (the paper uses Lemma 2.3(b) instead, which needs only the endpoint statement at level k).
P6  End-to-end: the Poisson mixture truncated to |M| <= k - 5 reproduces (1 - xS/k)^k - eps up to a small remainder.
"""
import sys, math, time
from fractions import Fraction as Fr
import mpmath as mp
from mpmath import iv

TAU = Fr(9, 20)
EPS0 = Fr(1, 200)
t0 = time.time()


def bt_mp(k, eps, r, scale=False):
    tau = mp.mpf(9) / 20
    e = mp.mpf(eps.numerator) / eps.denominator
    rho = 1 - e
    x = 5 * tau * rho
    first = (5 * tau ** r - x ** r * mp.mpf(k) ** (1 - r)) / r
    s = mp.mpf(0)
    m = 1
    while True:
        term = e ** m / m * mp.mpf(math.comb(k * m + r - 1, r))
        s += term
        if m > 3 and term < s * mp.mpf(10) ** (-(mp.mp.dps + 5)):
            break
        m += 1
    if scale:
        return first - (x / k) ** r * s, abs(first) + abs((x / k) ** r * s)
    return first - (x / k) ** r * s


def logE_exact(k, eps, R):
    rho = 1 - eps
    x = 5 * TAU * rho
    A = [Fr(math.comb(k, j)) * (-x / k) ** j for j in range(R + 1)]
    A[0] -= eps
    B = [Fr(math.comb(n + 4, 4)) * TAU ** n for n in range(R + 1)]
    E = [sum(A[i] * B[n - i] for i in range(n + 1)) / rho for n in range(R + 1)]
    assert E[0] == 1
    L = [Fr(0)] * (R + 1)
    for n in range(1, R + 1):
        L[n] = E[n] - sum((m * L[m] * E[n - m] for m in range(1, n)), Fr(0)) / n
        assert isinstance(L[n], Fr)
    return L


def F_lower(r, k):
    M = max(r, 60)
    L = 1
    for m in range(1, M + 1):
        L = L * m // math.gcd(L, m)
    N = 0
    for m in range(1, M + 1):
        N += math.comb(k * m + r - 1, r) * 200 ** (M - m) * (L // m)
    S = Fr(N, 200 ** M * L)
    rhoM = Fr((M + 1) ** r, 200 * M ** r)
    assert rhoM < 1
    termM = Fr(math.comb(k * M + r - 1, r), 200 ** M * M)
    S += termM * rhoM / (1 - rhoM)
    return (5 - Fr(5 ** r, k ** (r - 1))) / r - Fr(5 ** r, k ** r) * S


def main():
    mp.mp.dps = 50
    print('b_check_v2.py', flush=True)
    # P1
    worst = 0
    negs = []
    for k in (12, 40, 200):
        for eps in (Fr(1, 200), Fr(1, 1000)):
            R = 40
            L = logE_exact(k, eps, R)
            assert L[1] == 0, L[1]
            for r in range(1, R + 1):
                b, scl = bt_mp(k, eps, r, scale=True)
                ex = mp.mpf(L[r].numerator) / L[r].denominator
                rel = abs(ex - b) / scl
                worst = max(worst, rel)
                if r <= k and b < 0:
                    negs.append((k, eps, r))
    print('P1 bt_r formula vs exact series of log E_k (k = 12, 40, 200; eps = 1/200, 1/1000; r <= 40): '
          'max |diff|/(|part1|+|part2|) = %.2e; L_1 = 0 exactly' % float(worst), flush=True)
    print('P1 negative bt_r with r <= k (expected only for k < 40):', negs[:8], flush=True)
    # P2
    mins = []
    for (rr, kk) in [(range(2, 41), None), (range(41, 301), 'r')]:
        best = None
        for r in rr:
            k = 40 if kk is None else r
            v = r * F_lower(r, k)
            if best is None or v < best[0]:
                best = (v, r)
            if v <= 0:
                print('P2 FAIL r = %d k = %d: r F <= %s' % (r, k, float(v)), flush=True)
        mins.append(best)
    print('P2 Claim 1 exact: min r F(r,40) over 2 <= r <= 40 >= %.6f (at r = %d); min r F(r,r) over 40 < r <= 300 >= %.6f '
          '(at r = %d)   [%.1fs]' % (float(mins[0][0]), mins[0][1], float(mins[1][0]), mins[1][1], time.time() - t0),
          flush=True)
    # P3
    e0 = iv.mpf(1) / 200
    for s_txt in ('5.2', '5.25', '5.28'):
        s = iv.mpf(s_txt)
        assert (e0 * iv.exp(s)).b < 1
        r = 301
        B = r * (iv.mpf(5) / r) ** r + r * (5 / s) ** r * iv.exp(s) * (-iv.log(1 - e0 * iv.exp(s)))
        print('P3 s = %s: r = 301: subtracted terms <= %s, so r F(r,r) >= %s; ratio (5/s) = %s < 1' % (
            s_txt, mp.nstr(B.b, 6), mp.nstr((5 - B).a, 6), mp.nstr((5 / s).b, 6)), flush=True)
    print('P3 monotone: r q^r decreases for r > 1/log(1/q) = %s (q = 5/5.28); r (5/r)^r decreases for r >= 5' %
          mp.nstr(1 / mp.log(mp.mpf('5.28') / 5), 5), flush=True)
    # P4
    tau = iv.mpf(9) / 20
    z = iv.mpf(8) / 5
    Cz = 2 * (1 + tau) ** 5 * z ** 4 * (1 - tau * z) ** (-10) * iv.exp(-10 * tau * z)
    print('P4 Cz = 2(1+tau)^5 z^4 (1-tau z)^-10 e^{-10 tau z} in [%s, %s]  (< 21177: %s)' % (
        mp.nstr(Cz.a, 10), mp.nstr(Cz.b, 10), Cz.b < 21177), flush=True)

    # P5
    def Kfun(eps):
        v = mp.log(mp.mpf(21177) / (mp.mpf(eps.numerator) / eps.denominator)) / mp.log(mp.mpf(8) / 5)
        assert abs(v - mp.nint(v)) > mp.mpf(10) ** -20
        return int(mp.floor(v)) + 1

    def Kstar(eps):
        return max(45, Kfun(eps))

    def Kss(eps):
        ks = Kstar(eps)
        return -((-225 * ks) // 224) + 1

    for eps in (Fr(1, 200), Fr(1, 10 ** 4), Fr(1, 10 ** 5), Fr(1, 10 ** 6)):
        print('P5 eps = %s: K = %d, K* = %d, K** = %d' % (eps, Kfun(eps), Kstar(eps), Kss(eps)), flush=True)
    # brute-force bookkeeping of step (5)
    bad = 0
    nchk = 0
    for eps in (Fr(1, 200), Fr(1, 201), Fr(1, 1000), Fr(3, 10 ** 4), Fr(1, 10 ** 4), Fr(1, 10 ** 6)):
        K2 = Kss(eps)
        for k in list(range(K2, 3000)) + [10 ** 4, 10 ** 5 + 7]:
            g = 9 * (1 - eps) / (4 * k)
            jmax = math.floor(Fr(56, 25) / g)   # levels 9 <= j <= jmax: g <= 56/(25 j), Theorem 9.2 (X = 56/25)
            assert jmax >= 8
            for j in list(range(1, 9)) + list(range(max(9, jmax + 1), k + 1)):
                nchk += 1
                if j <= 3:
                    okj = g <= Fr(1, 2)
                elif j == 4:
                    okj = g <= Fr(79, 160)
                elif j == 5:
                    okj = g <= Fr(9, 20)
                elif j <= 8:
                    okj = g <= Fr(11, 5 * j)
                elif g <= Fr(56, 25 * j):
                    okj = True
                else:
                    epsj = 1 - Fr(j, k) * (1 - eps)
                    okj = (0 < epsj <= EPS0) and j >= Kstar(epsj) and j >= 40 and epsj >= eps and \
                          9 * (1 - epsj) / (4 * j) == g
                if not okj:
                    bad += 1
                    if bad < 5:
                        print('P5 uncovered level: eps = %s k = %d j = %d' % (eps, k, j), flush=True)
    print('P5 step (5) bookkeeping: %d (k, j) pairs checked, %d uncovered   [%.1fs]' % (nchk, bad, time.time() - t0),
          flush=True)
    # P6
    mp.mp.dps = 40
    for (k, eps) in ((30, Fr(1, 200)), (40, Fr(1, 500)), (60, Fr(1, 200))):
        tau_m = mp.mpf(9) / 20
        e = mp.mpf(eps.numerator) / eps.denominator
        rho = 1 - e
        x = 5 * tau_m * rho
        bts = {r: bt_mp(k, eps, r) for r in range(2, k + 1)}
        minbt = min(bts.values())
        cap = k - 5
        P = {0: [mp.mpf(1)] + [mp.mpf(0)] * k}
        for r in range(2, k + 1):
            b = bts[r]
            newP = {}
            for s, poly in P.items():
                i = 0
                powpoly = list(poly)
                while s + r * i <= cap:
                    w = mp.exp(-b) * b ** i / mp.factorial(i)
                    tgt = newP.setdefault(s + r * i, [mp.mpf(0)] * (k + 1))
                    for jj in range(k + 1):
                        tgt[jj] += w * powpoly[jj]
                    # powpoly *= (1 + S^r)
                    nxt = list(powpoly)
                    for jj in range(k, r - 1, -1):
                        nxt[jj] += powpoly[jj - r]
                    powpoly = nxt
                    i += 1
            P = newP
        G = [sum(P[s][jj] for s in P) for jj in range(k + 1)]
        f5 = [mp.binomial(5, i) * (-tau_m) ** i for i in range(6)]
        V = [rho * sum(f5[i] * G[jj - i] for i in range(6) if jj - i >= 0) for jj in range(k + 1)]
        target = [mp.binomial(k, jj) * (-x / k) ** jj for jj in range(k + 1)]
        target[0] -= e
        Rem = [target[jj] - V[jj] for jj in range(k + 1)]
        l1 = sum(abs(v) for v in Rem)
        qlb = e + Rem[0] + 2 * sum(min(mp.mpf(0), v) for v in Rem[1:])
        print('P6 k = %d eps = %s: min_r bt_r = %s; sum_j |Rem_j| = %s; q_k(x/k) >= eps + Rem_0 + 2 sum min(0, Rem_j) = %s;'
              ' Chernoff bound eps - Cz z^-k = %s' % (k, eps, mp.nstr(minbt, 5), mp.nstr(l1, 5), mp.nstr(qlb, 8),
                                                     mp.nstr(e - 21177 * (mp.mpf(8) / 5) ** (-k), 6)), flush=True)
    print('B_CHECK DONE  [%.1fs]' % (time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
