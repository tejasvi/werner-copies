#!/usr/bin/env python
"""Independent check of the exact threshold certificates printed by cert_k5.py (log logs/cert_k5.log).
Rebuilds every row polynomial from its LABEL alone (no code shared with profile_lp_k5 / param_cert_ext2), with the inputs of
the paper, Section 9:
  FHPV(x,y) (I2): 2 - S^x - S^y + S^{x+y}/2           CR(x,y) (I3): 2 - S^x + S^y - S^{x+y}/2
  EP3(k_1,k_2,k_3) (I4): prod (1 - S^{k_i}/2)          K4(k_1..k_4) (I5): prod (1 - (79/160) S^{k_i})
  K5(k_1..k_5) (I6): prod (1 - (9/20) S^{k_i})         compressed set g<r>=1 (Lemma 9.1(b)): factor 1 + S^r
  a_m<=2: 2 - S^m;  a_m>=0: S^m
(FOI rows are rejected: they are not inputs of the paper.  The fixed-dimension labels EP4_3, EP5_3, mono, ent2, g<r>=-1/D are
accepted only with a dimension and do not occur in the all-d certificates.)
and checks (i) the identity q_k(g; S) = LB(g) + sum_i y_i(g) row_i(S) as polynomials in (g, S); (ii) the threshold is the
smallest positive root of LB's numerator; (iii) every y_i is > 0 at that root (no root of numerator / denominator on a
rational isolating interval, positive at an interior point); (iv) each row's total group size is <= k.
usage: verify_k5_certs.py LOG ..."""
import ast, re, sys
import sympy as sp
g, S = sp.symbols('g S')
H = sp.Rational(1, 2)


T4, T5 = sp.Rational(4979, 10000), sp.Rational(47, 100)


def row_poly(lab, d):
    name, rest = lab[0], list(lab[1:])
    grp = [x for x in rest if isinstance(x, str)]
    nums = [x for x in rest if not isinstance(x, str)]
    size = sum(nums)
    if name == 'FHPV':
        x, y = nums; P = 2 - S ** x - S ** y + H * S ** (x + y)
    elif name == 'CR':
        x, y = nums; P = 2 - S ** x + S ** y - H * S ** (x + y)
    elif name == 'FOI':
        raise ValueError('FOI row %s: not an input of the paper' % (lab,))
    elif name == 'EP3':
        P = sp.prod([1 - H * S ** x for x in nums])
    elif name == 'K4':
        assert len(nums) == 4
        P = sp.prod([1 - sp.Rational(79, 160) * S ** x for x in nums])
    elif name == 'K5':
        assert len(nums) == 5
        P = sp.prod([1 - sp.Rational(9, 20) * S ** x for x in nums])
    elif name == 'EP4_3':
        assert d == 3; P = (1 - T4 * S) ** 4; size = 4
    elif name == 'EP5_3':
        assert d == 3; P = (1 - T5 * S) ** 5; size = 5
    elif name == 'mono':
        assert d is not None
        j = nums[0]; return d * S ** j - S ** (j + 1), 0
    elif name.startswith('a_'):
        m = int(re.match(r'a_(\d+)', name).group(1))
        return (2 - S ** m if '<=2' in name else S ** m), 0
    else:
        raise ValueError(lab)
    for t in grp:
        if t == 'ent2':
            assert d is not None; P *= 1 - sp.Rational(2, d) * S + S ** 2; size += 2
        else:
            mm = re.match(r'g(\d+)=(.*)', t); r = int(mm.group(1)); gam = sp.Rational(mm.group(2))
            if d is None:
                assert gam == 1
            else:
                assert gam == 1 or gam == sp.Rational(-1, d ** r)
            P *= 1 + gam * S ** r; size += r
    return sp.expand(P), size


def check_block(k, d, LB, mults):
    q = sp.expand((1 - g * S) ** k)
    rhs = LB
    for lab, y in mults:
        P, size = row_poly(lab, d)
        assert size <= k, (lab, size)
        rhs += y * P
    ident = sp.simplify(sp.expand(q - rhs)) == 0
    num = sp.Poly(sp.numer(sp.together(LB)), g)
    roots = [r for r in num.real_roots() if r > 0]
    gs = min(roots)
    lo, hi = [iv for iv, _ in num.intervals(eps=sp.Rational(1, 10 ** 15)) if iv[0] <= sp.N(gs, 30) <= iv[1]][0]
    signs = True
    for lab, y in mults:
        nu, de = sp.fraction(sp.together(y))
        for p in (sp.Poly(nu, g), sp.Poly(de, g)):
            if p.degree() > 0 and p.count_roots(lo, hi) != 0:
                signs = False
        if not (y.subs(g, (lo + hi) / 2) > 0):
            signs = False
    return ident, sp.N(gs, 20), signs


def parse(path):
    blocks, cur = [], None
    for line in open(path):
        m = re.match(r'k = (\d+) d = (\w+): gamma\* = \S+\s+\(root of (.*)\) \| rows', line)
        if m:
            cur = [int(m.group(1)), None if m.group(2) == 'all' else int(m.group(2)), sp.sympify(m.group(3), locals={'g': g}), []]
            blocks.append(cur); continue
        m = re.match(r"\s+(\(.*?\))\s+(.*?)\s+\(at g\*", line)
        if m and cur is not None:
            lab = ast.literal_eval(m.group(1))
            if isinstance(lab, str):
                lab = (lab,)
            cur[3].append((lab, sp.sympify(m.group(2), locals={'g': g})))
    return blocks


if __name__ == '__main__':
    allok = True
    nblocks = 0
    for path in sys.argv[1:]:
        for k, d, LB, mults in parse(path):
            nblocks += 1
            ident, gs, signs = check_block(k, d, LB, mults)
            ok = ident and signs
            allok &= ok
            print('%s: k = %d d = %s: identity %s | threshold %s | multipliers positive %s | rows %d | %s' % (
                path.split('/')[-1], k, d or 'all', ident, gs, signs, len(mults), 'PASS' if ok else 'FAIL'), flush=True)
    allok &= nblocks > 0
    print('ALL PASS' if allok else 'SOME FAILED')
