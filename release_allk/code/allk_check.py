#!/usr/bin/env python
"""Independent exact checker for the all-k certificate files (certs/*.json, written by allk_dump.py) of Theorem 9.2 of the paper.
No LP, no code shared with the row generators: every row polynomial is rebuilt from its LABEL alone, with the inputs of the
paper, Section 9:
  FHPV(x,y) (I2): 2 - S^x - S^y + S^{x+y}/2      CR(x,y) (I3): 2 - S^x + S^y - S^{x+y}/2
  EP3(k_1,k_2,k_3) (I4): prod (1 - S^{k_i}/2)     K4(k_1..k_4) (I5): prod (1 - (79/160) S^{k_i})
  K5(k_1..k_5) (I6): prod (1 - (9/20) S^{k_i})    compressed set g<r>=1 (Lemma 9.1(b)): factor (1 + S^r)
Any other label (for example an FOI row, which is not an input of the paper) makes the check fail.
Checks, with 0 <= a_j <= 2 and a_0 = 1:
(A) each k0 <= k < J: rows have total size <= k, y >= 0, slack_k = r_0 + 2 sum_{j>=1} min(0, r_j) > 0 with r = c(k) - sum y row;
(B) each J <= k <= K: with y_inf (or the per-k certificate), rows of size <= J, slack_k(J) - 2 TAIL > 0, where c_j = C(k,j)(-X/k)^j;
(C) delta_inf - E2/(K+1) - 2 TAIL > 0 with delta_inf recomputed from y_inf against e_j = (-X)^j/j!, E2 = sum_{even j<=J} X^j/(j-2)!,
    TAIL = X^{J+1}/(J+1)! / (1 - X/(J+2)) >= sum_{j>J} X^j/j!  (re-derived here, not read from the file).
With --no-k5, K5 rows are refused (negative control: the certificates need input (I6)).
usage: allk_check.py CERT.json [--no-k5]"""
import sys, json, re
from fractions import Fraction as Fr
from math import comb, factorial
C = json.load(open(sys.argv[1])); allow_k5 = '--no-k5' not in sys.argv
X = Fr(C['X']); J = C['J']; K0 = C['k0']; K = C['K']
H = Fr(1, 2)


def pmul(a, b, n):
    out = [Fr(0)] * n
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if i + j < n:
                    out[i + j] += x * y
    return out


def row(lab, n):
    name, rest = lab[0], lab[1:]
    nums = [x for x in rest if isinstance(x, int)]
    grp = [x for x in rest if isinstance(x, str)]
    size = sum(nums)
    P = [Fr(0)] * n
    def mono(e, c):
        if e < n:
            P[e] += c
    if name == 'FHPV':
        x, y = nums; mono(0, 2); mono(x, -1); mono(y, -1); mono(x + y, H)
    elif name == 'CR':
        x, y = nums; mono(0, 2); mono(x, -1); mono(y, 1); mono(x + y, -H)
    elif name in ('EP3', 'K4', 'K5'):
        tau = {'EP3': H, 'K4': Fr(79, 160), 'K5': Fr(9, 20)}[name]
        assert len(nums) == {'EP3': 3, 'K4': 4, 'K5': 5}[name], lab
        if name == 'K5':
            assert allow_k5, 'K5 row refused (--no-k5)'
        P[0] = Fr(1)
        for x in nums:
            f = [Fr(0)] * n; f[0] = Fr(1)
            if x < n:
                f[x] = -tau
            P = pmul(P, f, n)
    else:
        raise ValueError(lab)
    for t in grp:
        m = re.match(r'g(\d+)=1$', t)
        assert m, t
        r = int(m.group(1)); size += r
        f = [Fr(0)] * n; f[0] = Fr(1)
        if r < n:
            f[r] = Fr(1)
        P = pmul(P, f, n)
    return P, size


def slack(cert_rows, c, n, maxsize):
    r = list(c) + [Fr(0)] * (n - len(c))
    for lab, ys in cert_rows:
        y = Fr(ys)
        assert y >= 0
        P, size = row(tuple(lab), n)
        assert size <= maxsize, (lab, size, maxsize)
        for j in range(n):
            r[j] -= y * P[j]
    return r[0] + 2 * sum(min(Fr(0), v) for v in r[1:])


TAIL = X ** (J + 1) / factorial(J + 1) / (1 - X / (J + 2))
assert X / (J + 2) < 1
worstA = None
for k in range(K0, J):
    rows_k = C['A'][str(k)]
    c = [Fr(comb(k, j)) * (-X / k) ** j for j in range(k + 1)]
    s = slack(rows_k, c, k + 1, k)
    assert s > 0, ('A', k, float(s))
    worstA = s if worstA is None or s < worstA else worstA
yinf = C['yinf']
e = [(-X) ** j / factorial(j) for j in range(J + 1)]
dinf = slack(yinf, e, J + 1, J)
worstB = None; nfix = 0
for k in range(J, K + 1):
    c = [Fr(comb(k, j)) * (-X / k) ** j for j in range(J + 1)]
    rows_k = C['B'].get(str(k))
    if rows_k is None:
        s = slack(yinf, c, J + 1, J) - 2 * TAIL
    else:
        s = slack(rows_k, c, J + 1, J) - 2 * TAIL; nfix += 1
    assert s > 0, ('B', k, float(s))
    worstB = s if worstB is None or s < worstB else worstB
E2 = sum(X ** j / factorial(j - 2) for j in range(2, J + 1, 2))
slackC = dinf - E2 / (K + 1) - 2 * TAIL
assert slackC > 0, ('C', float(slackC))
print('%s: X = %s J = %d k0 = %d K = %d | (A) k = %d..%d min slack %.4e | (B) %d k, %d per-k fixes, min slack %.4e | (C) %.4e > 0 | ALL CHECKS PASS: q_k(%s/k) >= 0 for every k >= %d' % (
    sys.argv[1].split('/')[-1], X, J, K0, K, K0, J - 1, float(worstA) if worstA is not None else float('nan'), K - J + 1, nfix,
    float(worstB), float(slackC), X, K0), flush=True)
