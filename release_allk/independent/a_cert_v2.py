#!/usr/bin/env python3
"""Independent construction for Theorem 9.2 of the paper: exact slack certificates for every k, with its own large-k argument.
Written from the definitions of Section 9 only; it shares no code with ../code.

Profile: a_0 = 1, 0 <= a_j <= 2 (a_j >= 0 trivially; a_j <= 2 is EP_1 on one group of j copies, Lemma 9.1).
q_k(X/k) = sum_j b_j a_j with b_j = C(k,j) (-X/k)^j.
Rows (all dimensions; Lemma 9.1(a) groups and frozen copies, Lemma 9.1(b) compressed sets):
  base(S) * prod_{compressed groups g} (1 + S^{r_g}),  S^j read as a_j, total size (base groups + compressed) <= k.
  base: TB(s)      = 2 - S^s                              (EP_1, trace bound)
        FHPV(a,b)  = 2 - S^a - S^b + S^{a+b}/2            (EP_2 in FHPV form)
        CR(a,b)    = 2 - S^a + S^b - S^{a+b}/2            (Costa Rico (45): a_a - a_b <= 2 - a_{a+b}/2, ordered)
        EP3(a,b,c) = prod (1 - S^x/2)
        K4(a..d)   = prod (1 - (79/160) S^x)
        K5(a..e)   = prod (1 - (9/20) S^x)               (I6)
Certificate: y >= 0, r = b - R^T y; then q >= r_0 + 2 sum_{j>=1} min(0, r_j)   (exact rationals).
Tail k >= J with rows of total size <= J: on an interval [ka, kb] the vector b(k) is >= the worst-case vector
  bw_j = C(ka,j)(X/ka)^j (j even), -C(kb,j)(X/kb)^j (j odd; -X^j/j! if kb = inf), and the degrees j > J add at least
  -2 sum_{odd j > J} X^j/j!.  The slack is monotone in b, so slack(bw) > 0 certifies every k in [ka, kb].
usage: a_cert_v2.py X_num/X_den J kmin [kmax_perk]
"""
import sys, time, math
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

T4 = Fr(79, 160)
T5 = Fr(9, 20)
HALF = Fr(1, 2)


def parts_upto(R, maxpart=None):
    """all multisets (non-increasing tuples) of positive integers with sum <= R"""
    if maxpart is None:
        maxpart = R
    yield ()
    for p in range(min(R, maxpart), 0, -1):
        for rest in parts_upto(R - p, p):
            yield (p,) + rest


def parts_exact_m(m, R, maxpart=None):
    """non-increasing tuples of exactly m positive integers with sum <= R"""
    if maxpart is None:
        maxpart = R
    if m == 0:
        yield ()
        return
    for p in range(min(R - (m - 1), maxpart), 0, -1):
        for rest in parts_exact_m(m - 1, R - p, p):
            yield (p,) + rest


def pmul(p, q):
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    r[i + j] += a * b
    return r


def mono(c0, terms):
    """polynomial c0 + sum c S^e"""
    deg = max([0] + [e for c, e in terms])
    p = [Fr(0)] * (deg + 1)
    p[0] += c0
    for c, e in terms:
        p[e] += c
    return p


def prod_factor(sizes, t):
    p = [Fr(1)]
    for s in sizes:
        p = pmul(p, mono(Fr(1), [(-t, s)]))
    return p


def bases(n):
    """(label, polynomial, total size) for every base row with total size <= n"""
    out = []
    for s in range(1, n + 1):
        out.append(('TB(%d)' % s, mono(Fr(2), [(Fr(-1), s)]), s))
    for (a, b) in parts_exact_m(2, n):
        out.append(('FHPV(%d,%d)' % (a, b), mono(Fr(2), [(Fr(-1), a), (Fr(-1), b), (HALF, a + b)]), a + b))
    for a in range(1, n):
        for b in range(1, n - a + 1):
            if a != b:
                out.append(('CR(%d,%d)' % (a, b), mono(Fr(2), [(Fr(-1), a), (Fr(1), b), (-HALF, a + b)]), a + b))
    for sz in parts_exact_m(3, n):
        out.append(('EP3' + str(sz), prod_factor(sz, HALF), sum(sz)))
    for sz in parts_exact_m(4, n):
        out.append(('K4' + str(sz), prod_factor(sz, T4), sum(sz)))
    for sz in parts_exact_m(5, n):
        out.append(('K5' + str(sz), prod_factor(sz, T5), sum(sz)))
    return out


def build_rows(n, use_k5=True):
    rows = {}
    for lab, p, s in bases(n):
        if (not use_k5) and lab.startswith('K5'):
            continue
        for comp in parts_upto(n - s):
            q = p
            for r in comp:
                q = pmul(q, mono(Fr(1), [(Fr(1), r)]))
            assert len(q) - 1 <= n
            v = tuple(q + [Fr(0)] * (n + 1 - len(q)))
            if v not in rows:
                rows[v] = lab + ('+c' + str(list(comp)) if comp else '')
    labs = list(rows.values())
    R = list(rows.keys())
    return labs, R


def b_exact(X, k, n):
    return [Fr(math.comb(k, j)) * (-X / k) ** j for j in range(n + 1)]


def b_worst(X, ka, kb, n):
    b = [Fr(1)]
    for j in range(1, n + 1):
        if j % 2 == 0:
            b.append(Fr(math.comb(ka, j)) * (X / ka) ** j)
        elif kb is None:
            b.append(-(X ** j) / math.factorial(j))
        else:
            b.append(-Fr(math.comb(kb, j)) * (X / kb) ** j)
    return b


def tail_bound(X, J):
    """rigorous upper bound of sum_{odd j > J} X^j / j!"""
    j0 = J + 1 if (J + 1) % 2 == 1 else J + 2
    assert X < j0 + 1
    return (X ** j0 / math.factorial(j0)) / (1 - X / (j0 + 1))


def solve_lp(Rf, bf):
    """maximize r_0 - 2 sum z_j over y >= 0, z >= 0, z_j >= -(b_j - (R^T y)_j); returns (lp slack, y)"""
    N, n1 = Rf.shape
    n = n1 - 1
    c = np.concatenate([Rf[:, 0], 2.0 * np.ones(n)])
    A = np.hstack([Rf[:, 1:].T, -np.eye(n)])
    res = linprog(c, A_ub=A, b_ub=bf[1:], bounds=[(0, None)] * (N + n), method='highs')
    if res.status != 0:
        return None, None
    return 1.0 - res.fun, res.x[:N]


def exact_slack(R, y, b, tail):
    """exact slack r_0 + 2 sum min(0, r_j) - 2 tail, y given as floats (taken exactly as binary rationals)"""
    n = len(b) - 1
    r = list(b)
    used = []
    for i, yi in enumerate(y):
        if yi > 0:
            fy = Fr(float(yi))
            used.append(i)
            row = R[i]
            for j in range(n + 1):
                if row[j]:
                    r[j] -= fy * row[j]
    s = r[0] + 2 * sum(min(Fr(0), rj) for rj in r[1:]) - 2 * tail
    return s, used


def certify(R, Rf, b, tail, active=None):
    bf = np.array([float(v) for v in b])
    if active is not None:
        idx = sorted(active)
        lp, y = solve_lp(Rf[idx], bf)
        if y is None:
            return None, None, None
        yy = np.zeros(len(R))
        yy[idx] = y
        y = yy
    else:
        lp, y = solve_lp(Rf, bf)
        if y is None:
            return None, None, None
    s, used = exact_slack(R, y, b, tail)
    return s, used, lp


def main():
    num, den = sys.argv[1].split('/')
    X = Fr(int(num), int(den))
    J = int(sys.argv[2])
    kmin = int(sys.argv[3])
    use_k5 = (len(sys.argv) <= 4 or sys.argv[4] != 'nok5')
    t0 = time.time()
    print('a_cert.py X = %s = %.6f, J = %d, kmin = %d, K5 rows: %s' % (X, float(X), J, kmin, use_k5), flush=True)
    ok = True
    covered = []
    bases_used = set()
    minslack = None
    cache = {}

    def rows_for(n):
        if n not in cache:
            labs, R = build_rows(n, use_k5)
            Rf = np.array([[float(v) for v in row] for row in R])
            cache[n] = (labs, R, Rf)
            print('  rows with total size <= %d: %d   (%.1fs)' % (n, len(R), time.time() - t0), flush=True)
        return cache[n]

    # Part 1: per-k certificates for kmin <= k < J, all rows of total size <= k (exact b, no tail).
    for k in range(kmin, J):
        labs, R, Rf = rows_for(k)
        b = b_exact(X, k, k)
        s, used, lp = certify(R, Rf, b, Fr(0))
        good = s is not None and s > 0
        ok &= good
        minslack = s if minslack is None or (s is not None and s < minslack) else minslack
        print('PERK k=%d rows<=%d LP %.6e exact slack %s (%.6e) used %d rows %s' % (
            k, k, lp, 'NONE' if s is None else ('%s/%s' % (s.numerator.bit_length(), s.denominator.bit_length())),
            float(s) if s is not None else float('nan'), len(used) if used else 0, 'OK' if good else 'FAIL'), flush=True)
        if good:
            print('   rows:', ', '.join(labs[i] for i in used), flush=True)
            covered.append((k, k))
            bases_used |= set(labs[i].split('(')[0] for i in used)
    # Part 2: k >= J by intervals, rows of total size <= J.
    labs, R, Rf = rows_for(J)
    tail = tail_bound(X, J)
    print('  tail bound sum_{odd j > %d} X^j/j! <= %.3e' % (J, float(tail)), flush=True)
    sl, used, lp = certify(R, Rf, b_worst(X, 10 ** 12, None, J), tail)
    print('LIMIT-ish [1e12, inf): LP %.6e exact %.6e' % (lp, float(sl)), flush=True)
    active = set(used)
    ka = J
    step = 1
    nint = 0
    nfull = 0
    while True:
        # first try the infinite interval [ka, inf)
        s, u, lp = certify(R, Rf, b_worst(X, ka, None, J), tail, active)
        if s is not None and s > 0:
            print('INTERVAL [%d, inf): exact slack %.6e  (rows %d)' % (ka, float(s), len(u)), flush=True)
            covered.append((ka, None))
            bases_used |= set(labs[i].split('(')[0] for i in u)
            minslack = s if (minslack is None or s < minslack) else minslack
            nint += 1
            break
        kb = ka + step - 1
        s, u, lp = certify(R, Rf, b_worst(X, ka, kb, J), tail, active)
        if s is None or s <= 0:
            # shrink
            if step > 1:
                step = max(1, step // 2)
                continue
            # single k fails with active set: full LP
            nfull += 1
            s, u, lp = certify(R, Rf, b_worst(X, ka, kb, J), tail)
            if s is None or s <= 0:
                print('FAIL at k = %d (full LP %s)' % (ka, lp), flush=True)
                ok = False
                break
            active |= set(u)
        minslack = s if (minslack is None or s < minslack) else minslack
        nint += 1
        covered.append((ka, kb))
        bases_used |= set(labs[i].split('(')[0] for i in u)
        if True:
            print('  interval [%d, %d] slack %.3e  (step %d, active %d, %.1fs)' % (ka, kb, float(s), step, len(active),
                                                                               time.time() - t0), flush=True)
        ka = kb + 1
        step = step * 2
        if time.time() - t0 > 560:
            print('TIME LIMIT at ka = %d' % ka, flush=True)
            ok = False
            break
    print('intervals used: %d, full-LP fallbacks: %d, active rows: %d' % (nint, nfull, len(active)), flush=True)
    print('active rows:', ', '.join(sorted(labs[i] for i in active)), flush=True)
    print('MIN EXACT SLACK %.6e' % float(minslack), flush=True)
    contiguous = len(covered) > 0 and covered[0][0] == kmin and covered[-1][1] is None and all(covered[i + 1][0] == covered[i][1] + 1 for i in range(len(covered) - 1))
    print('COVERAGE: %d pieces, first %s, last %s, contiguous from kmin to infinity: %s' % (len(covered), covered[0], covered[-1], contiguous), flush=True)
    print('BASE TYPES USED IN ALL CERTIFICATES:', sorted(bases_used), flush=True)
    ok = ok and contiguous
    print('RESULT X=%s: %s  (%.1fs)' % (X, 'ALL k >= %d CERTIFIED' % kmin if ok else 'GAP', time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
