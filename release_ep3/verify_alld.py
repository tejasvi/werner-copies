#!/usr/bin/env python3
"""verify_alld.py -- standalone verifier: EP_3 holds for every local dimension d >= 9.

Input: the compact certificate ep3_alld.pkl.xz (a polynomial-in-s certificate, s = 1/d in [0, 1/9], plus the data of
a two-stage exact correction).  Imports only ep3core (this directory), numpy, python-flint and the standard library;
nothing from the construction code.

Checks (exact unless stated; the stage-2 inequality uses rigorous floating-point error bounds):
 [A] structure: every site module is a diagram compression J(n) = D(n) C with the standard diagram keys of its label;
     local map entries are eps * n^c with c <= 2f (loop counting, asserted in ep3core); delta_t = 2 * (sum of the
     site labels' f), so the verifier columns, the objective and the residual are polynomials in s of known degree;
 [B] margins: every Bernstein coefficient block of the base certificate satisfies C_tj - m T_r T_r^T >= 0 (exact
     characteristic polynomial), hence Z_t(s) / s^delta_t >= m T_r T_r^T for every s in [0, 1/9];
 [C] stage 1: the explicit polynomial correction satisfies ||Delta D_t(s)||_op <= eps1 on [0, 1/9];
 [D] residual: r'(s) = c - (verifier map)(certificate + stage-1 correction), exactly at 38 nodes (degree <= 32);
 [E] stage-2 columns: the square column subset S at 18 nodes, modulo primes (degree <= 12 per column);
 [F] consistency: W(s)^T A_S(s) == 0 (residues modulo primes whose product exceeds twice an a-priori height bound,
     18 nodes, degree <= 17), W(s)^T r'(s) == 0 (exact, 38 nodes, degree <= 37), rank W(1/9) = nrow - |R| (mod p);
 [G] stage 2 (Neumann): verifier-computed approximate inverses B(s) of the normalised A_RS(s):
     theta = sup ||I - A_RS B|| < 1 and the block correction eps2 (mid-rad floating point, Lebesgue constants);
 [H] eps1 + sqrt(2) eps2 < m.
Conclusion (Lemma RA): for every s in [0, 1/9], delta(s) = B (I - E)^{-1} r'_R(s) solves the identity in ALL rows
(theta < 1 gives rank A_RS(s) = |R|; [F] gives generic rank A_S <= |R| and r' in the range of A_S, by continuity of the
range projector at constant rank), every block stays positive definite, and at s = 1/d all data are rational: an exact
certificate of the diagram relaxation at d, which is valid since every compression of a PSD operator is PSD.
Usage: python3 verify_alld.py ep3_alld.pkl.xz [--workers N]
"""
import argparse
import itertools
import lzma
import math
import multiprocessing as mp
import os
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import flint

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ep3core as E

sys.set_int_max_str_digits(0)
U = 2.0 ** -53
G = {}
NRES, BRES = 38, 14          # residual nodes: 38 Chebyshev-Lobatto points rounded to 2^-14
NCOL, BCOL = 18, 12          # column nodes: 18 Chebyshev-Lobatto points rounded to 2^-12
QB = 20                      # degree of the interpolated approximate inverse


def log(s):
    print('[%7.1fs] %s' % (time.time() - G['t0'], s), flush=True)


def gam(n):
    return n * U / (1 - n * U)


def upnorm(M):
    """rigorous upper bound of ||M||_F for a float array."""
    return float(np.linalg.norm(M)) * (1 + gam(M.size + 2)) * (1 + 2 * U) + 1e-280


def up(x):
    """a float >= the exact rational / float x."""
    return math.nextafter(float(x), math.inf)


def cheb_nodes(N, smax, bits):
    out = [Fraction(round((1 - math.cos(math.pi * c / (N - 1))) / 2 * smax * 2 ** bits), 2 ** bits) for c in range(N)]
    assert len(set(out)) == N and out[0] == 0 and 0 < out[-1] <= Fraction(1, 9)
    return out


def cheb_float(N, smax):
    x = np.cos(np.pi * np.arange(N) / (N - 1))[::-1]
    return (x + 1) / 2 * smax


def lagrange_w(nodes, t):
    w = []
    for i, x in enumerate(nodes):
        v = Fraction(1)
        for j, y in enumerate(nodes):
            if j != i:
                v *= (t - y) / (x - y)
        w.append(v)
    return w


def lebesgue(nodes, smax):
    """rigorous upper bound of max_{s in [0, smax]} sum_j |l_j(s)| for float nodes (grid + Markov remainder)."""
    N = len(nodes)
    n = N - 1
    M = int(40 * N * n * n) + 1001
    best = 0.0
    for g0 in range(0, M, 200000):
        sg = np.linspace(0, smax, M)[g0:g0 + 200000]
        tot = np.zeros(len(sg))
        for c in range(N):
            l_ = np.ones(len(sg))
            for c2 in range(N):
                if c2 != c:
                    l_ *= (sg - nodes[c2]) / (nodes[c] - nodes[c2])
            tot += np.abs(l_)
        best = max(best, float(tot.max()))
    best = best / ((1 - gam(4 * n + 2)) * (1 - gam(N)))
    fac = N * n * n / (M - 1)
    assert fac < 0.5
    return best / (1 - fac)


def bern_num(p, i, m, b):
    """numerator of B_{i,p}(9s) at s = m / 2^b, over the denominator 2^{b p}: C(p,i) (9m)^i (2^b - 9m)^{p-i}."""
    return math.comb(p, i) * (9 * m) ** i * (2 ** b - 9 * m) ** (p - i)


# ---------------------------------------------------------------- [A] structure
def diagram_keys(m, cut, lab):
    f, lam, mu = lab
    nc = [s for s in range(m) if s not in cut]
    cs = list(cut)
    top = [r for r, x in enumerate(lam) for _ in range(x)]
    bot = [-1 - r for r, x in enumerate(mu) for _ in range(x)]

    def fillings(slots, values):
        return sorted({tuple(zip(slots, perm)) for perm in itertools.permutations(values)})
    out = set()
    for A in itertools.combinations(nc, f):
        for B in itertools.permutations(cs, f):
            pairs = list(zip(A, B))
            rest_nc = [s for s in nc if s not in A]
            rest_c = [s for s in cs if s not in B]
            for fa in fillings(rest_nc, top):
                for fb in fillings(rest_c, bot):
                    out.add((tuple(sorted(pairs)), fa, fb))
    return sorted(out)


def check_structure(pkg):
    k = pkg['k']
    nlab = 0
    for (m, cut), labs in pkg['diagrams'].items():
        for lab, (keys, C) in labs.items():
            f, lam, mu = lab
            assert sum(lam) + f == m - len(cut) and sum(mu) + f == len(cut), 'label does not fit the cut'
            assert len(lam) + len(mu) <= 4 - 2 * f
            kk = [tuple(tuple(tuple(y) for y in x) for x in key) for key in keys]
            assert sorted(kk) == diagram_keys(m, cut, lab), 'non-standard diagram keys'
            assert all(int(x) == x for row in C for x in row)
            nlab += 1
    q1 = pkg['stage1']['q']
    deg = 4 * k
    for t in pkg['types']:
        fs = [E.parse_site_key(key)[1][0] for key in t['modules'][:k]]
        assert t['delta'] == 2 * sum(fs) <= 4 * k, 'delta_t != 2 sum f'
        deg = max(deg, t['delta'] + max(t['p'], q1))
    for it in pkg['eq_items']:
        deg = max(deg, k + len(it['mu']) - 1)
    deg = max(deg, k + q1)
    log('[A] %d diagram labels with standard keys and integer C; delta_t = 2 sum f for all %d types; '
        'columns have degree <= 4k = %d, the residual degree <= %d' % (nlab, len(pkg['types']), 4 * k, deg))
    return deg


# ---------------------------------------------------------------- [B] margins
def margin_task(ti):
    pkg = G['pkg']
    t = pkg['types'][ti]
    m = Fraction(pkg['margin'])
    r = t['r']
    T = flint.fmpz_mat([[int(x) for x in row] for row in t['T']])
    TT = T * T.transpose()
    bad = 0
    for Cn in t['Cnum']:
        M = flint.fmpz_mat(r, r, [Cn[i * r + j] * 2 ** 80 * m.denominator for i in range(r) for j in range(r)])
        M = M - TT * (m.numerator * 2 ** t['Cexp'])
        Z = [[int(M[i, j]) for j in range(r)] for i in range(r)]
        bad += not E.psd_charpoly(Z)
    return ti, bad, len(t['Cnum'])


# ---------------------------------------------------------------- [D] residual at one node
def stage1_tables(pkg):
    blk, eq = {}, {}
    for c in pkg['stage1']['cols']:
        key = c['col']
        if key[0] == 'blk':
            blk.setdefault(key[1], []).append((key[2], key[3], c['mant'], c['exp']))
        else:
            eq[(key[1], tuple(key[2]))] = (c['mant'], c['exp'])
    return blk, eq


def residual_task(j):
    pkg, rx = G['pkg'], G['rx']
    s = G['res_nodes'][j]
    m, b = s.numerator * (2 ** BRES // s.denominator), BRES          # s = m / 2^b
    q1 = pkg['stage1']['q']
    b1 = [bern_num(q1, i, m, b) for i in range(q1 + 1)]                  # / 2^{b q1}
    Ps = []
    for ti, t in enumerate(pkg['types']):
        r, p = t['r'], t['p']
        bp = [bern_num(p, i, m, b) for i in range(p + 1)]                 # / 2^{b p}
        Cs = flint.fmpz_mat(r, r)
        for i in range(p + 1):
            Cs += flint.fmpz_mat(r, r, t['Cnum'][i]) * bp[i]
        e_base = b * p + t['Cexp']
        corr = G['s1blk'].get(ti)
        if corr:
            emax = max(c[3] for c in corr)
            Dm = [[0] * r for _ in range(r)]
            for a, bb, mant, ex in corr:
                val = sum(b1[i] * mant[i] for i in range(q1 + 1)) * 2 ** (emax - ex)
                Dm[a][bb] = val
                Dm[bb][a] = val
            T = flint.fmpz_mat([[int(x) for x in row] for row in t['T']])
            TDT = T * flint.fmpz_mat(Dm) * T.transpose()                  # / 2^{80 + emax + b q1}
            e_corr = 80 + emax + b * q1
            e = max(e_base, e_corr)
            tot = Cs * 2 ** (e - e_base) + TDT * 2 ** (e - e_corr)
        else:
            e, tot = e_base, Cs
        Ps.append([[Fraction(int(tot[a, c]), 2 ** e) for c in range(r)] for a in range(r)])
    mu = {}
    for it in pkg['eq_items']:
        pm = len(it['mu']) - 1
        v = sum(bern_num(pm, i, m, b) * it['mu'][i] for i in range(pm + 1))
        mu.setdefault(it['group'], {})[tuple(it['o'])] = Fraction(v, 2 ** (b * pm + it['muexp']))
    for (g, o), (mant, ex) in G['s1eq'].items():
        v = Fraction(sum(b1[i] * mant[i] for i in range(q1 + 1)), 2 ** (b * q1 + ex))
        d_ = mu.setdefault(g, {})
        d_[o] = d_.get(o, Fraction(0)) + v
    acc = rx.residual(s, Ps, mu, smode=True)
    r = [x for f in E.FAMILIES for x in acc[f]]
    # W(s)^T r'(s) at this node, exactly (integer arithmetic after clearing the denominator)
    D = 1
    for x in r:
        D = D * x.denominator // math.gcd(D, x.denominator)
    ri = [int(x * D) for x in r]
    bad = 0
    for v in pkg['W']['vperp']:
        bad += sum(val * ri[i] for i, val in v['ent'].items()) != 0
    dw = pkg['W']['deg']
    for mv in pkg['W']['moving']:
        tot = 0
        for e, coef in enumerate(mv['coef']):
            tot += sum(val * ri[i] for i, val in coef.items()) * m ** e * 2 ** (b * (dw - e))
        bad += tot != 0
    return j, (r, bad)


# ---------------------------------------------------------------- [E] S columns modulo one prime at one node
def s_columns(x, p, ce, pkg, rx):
    nrow = pkg['nrow']
    S = pkg['stage2']['S']
    out = np.zeros((nrow, len(S)), dtype=np.int64)
    off, o_ = {}, 0
    for f in E.FAMILIES:
        off[f] = o_
        o_ += rx.orb[f][1]
    bytype, eqs = {}, []
    for c, key in enumerate(S):
        if key[0] == 'blk':
            bytype.setdefault(key[1], []).append((c, key[2], key[3]))
        else:
            eqs.append((c, key[1], tuple(key[2])))
    for ti, lst in bytype.items():
        T = np.array(pkg['types'][ti]['T'], dtype=object)
        Zl = []
        for (c, a, b) in lst:
            Z = np.outer(T[:, a], T[:, b])
            if a != b:
                Z = Z + np.outer(T[:, b], T[:, a])
            Zl.append(Z.tolist())
        res = ce.type_columns(x, True, ti, Zl, p)
        for f, arr in res.items():
            for jj, (c, _, _) in enumerate(lst):
                out[off[f]:off[f] + rx.orb[f][1], c] = arr[jj]
    if eqs:
        res = ce.eq_columns(x, True, [(g, o) for _, g, o in eqs], p)
        for f, arr in res.items():
            for jj, (c, _, _) in enumerate(eqs):
                out[off[f]:off[f] + rx.orb[f][1], c] = arr[jj]
    return out


def column_task(arg):
    j, p = arg
    pkg, rx, ce = G['pkg'], G['rx'], G['ce']
    s = G['col_nodes'][j]
    x = s.numerator * pow(s.denominator, -1, p) % p
    nrow = pkg['nrow']
    out = s_columns(x, p, ce, pkg, rx)
    bad = 0
    for v in pkg['W']['vperp']:
        idx = np.array(list(v['ent'].keys()))
        val = np.array([y % p for y in v['ent'].values()], dtype=np.int64)
        bad += bool(np.any((val[:, None] * out[idx, :]).sum(axis=0) % p))
    dw = pkg['W']['deg']
    sp = [pow(x, e, p) for e in range(dw + 1)]
    for mv in pkg['W']['moving']:
        w = np.zeros(nrow, dtype=np.int64)
        for e, coef in enumerate(mv['coef']):
            for i, val in coef.items():
                w[i] = (w[i] + (val % p) * sp[e]) % p
        acc = np.zeros(out.shape[1], dtype=np.int64)
        for c0 in range(0, nrow, 64):
            acc = (acc + w[c0:c0 + 64] @ out[c0:c0 + 64, :]) % p
        bad += bool(np.any(acc))
    R = pkg['stage2']['R']
    fn = os.path.join(G['tmp'], 'AS_%d_%d.npy' % (j, p))
    np.save(fn, out[R, :].astype(np.int32))
    return j, p, bad


# ---------------------------------------------------------------- height bounds for [E]/[F]
def height_bounds(pkg, rx):
    """For every column node: an upper bound H on |N| for every S column, where N = 2^{80 + b delta} a(s) (block) or
    2^{b k} e(s) (equality) is the integer whose residues are computed; and Wb = max over W vectors of
    sum_i |den * 2^{b deg} w_i(s)| (integer scaling of the left-kernel vectors)."""
    k = pkg['k']
    b = BCOL
    maxorb = 0
    for f in E.FAMILIES:
        oid, nor = rx.orb[f]
        maxorb = max(maxorb, int(np.bincount(oid.ravel()).max()))
    S = pkg['stage2']['S']
    blkcols = {}
    for key in S:
        if key[0] == 'blk':
            blkcols.setdefault(key[1], []).append((key[2], key[3]))
    eqcols = [(key[1], tuple(key[2])) for key in S if key[0] == 'eq']
    Hs, Wbs = [], []
    ce = G['ce']
    for s in G['col_nodes']:
        m = s.numerator * (2 ** b // s.denominator)
        H = 0
        for ti, lst in blkcols.items():
            t = pkg['types'][ti]
            mods = t['modules']
            T = np.array(t['T'], dtype=object)
            Wm = np.array(t['W'], dtype=object)
            dims = [rx.dims(mm, 'a' if l == k else 's') for l, mm in enumerate(mods)]
            nn = int(np.prod(dims))
            for (g, r, s_) in ce.block_pairs[ti]:
                f, kpos, lpos, cut = g
                amax = 1
                for l, mm in enumerate(mods):
                    if l == k:
                        A = rx.local_rows(mm, 'a', 2, kpos, lpos, False)
                    else:
                        M = rx.site_module(mm)
                        A = [M.local_s(s, E.op_edges(pp, kpos, lpos)) * 2 ** (b * 2 * M.f) for pp in E.PERMS]
                    amax *= max(abs(int(v)) for a_ in A for v in np.asarray(a_).ravel())
                Wr, Ws = Wm[r * nn:(r + 1) * nn], Wm[s_ * nn:(s_ + 1) * nn]
                ur = [sum(abs(int(Wr[X, a_])) for X in range(nn)) for a_ in range(Wm.shape[1])]
                us = [sum(abs(int(Ws[X, a_])) for X in range(nn)) for a_ in range(Wm.shape[1])]
                aT = [[abs(int(x)) for x in row] for row in t['T']]
                for (a, bb) in lst:
                    # sum |W_r Z W_s^T| <= u_r^T |Z| u_s with |Z| <= |T e_a||T e_b|^T + |T e_b||T e_a|^T
                    ta = sum(ur[i] * aT[i][a] for i in range(len(ur)))
                    tb = sum(us[i] * aT[i][bb] for i in range(len(us)))
                    ta2 = sum(ur[i] * aT[i][bb] for i in range(len(ur)))
                    tb2 = sum(us[i] * aT[i][a] for i in range(len(us)))
                    l1 = ta * tb + (ta2 * tb2 if a != bb else 0)
                    H = max(H, maxorb * l1 * amax * len(ce.block_pairs[ti]))
        for (g, o) in eqcols:
            tot = 0
            for part in pkg['eq_groups'][g]['parts']:
                pr = maxorb
                for l in range(k + 1):
                    Es = rx.eq_local(s, part['local'][l], True)
                    sc = 2 ** b if part['local'][l][0] == 'S' else 1
                    pr *= max(abs(int(v * sc)) for v in Es[o[l]])
                tot += pr
            H = max(H, tot)
        dw = pkg['W']['deg']
        Wb = max(sum(abs(y) for y in v['ent'].values()) for v in pkg['W']['vperp'])
        for mv in pkg['W']['moving']:
            tot = {}
            for e, coef in enumerate(mv['coef']):
                for i, val in coef.items():
                    tot[i] = tot.get(i, 0) + val * m ** e * 2 ** (b * (dw - e))
            Wb = max(Wb, sum(abs(y) for y in tot.values()))
        Hs.append(H)
        Wbs.append(Wb)
    return Hs, Wbs


# ---------------------------------------------------------------- CRT (balanced mixed radix) to floats
def crt_float(res_list, primes):
    """res_list[i]: int64 residues mod primes[i] of the same integer matrix N (|N| < prod(primes)/2).  Returns
    (float approximation of N, rigorous relative error bound)."""
    P = len(primes)
    t = []
    for i in range(P):
        x = res_list[i].astype(np.int64) % primes[i]
        for jj in range(i):
            x = ((x - t[jj]) % primes[i]) * pow(primes[jj], -1, primes[i]) % primes[i]
        x = np.where(x > primes[i] // 2, x - primes[i], x)                # balanced digit
        t.append(x)
    v = t[P - 1].astype(np.float64)
    for i in range(P - 2, -1, -1):
        v = t[i].astype(np.float64) + float(primes[i]) * v
    # Horner x_i = t_i + p_i x_{i+1} with balanced digits |t_i| <= p_i/2: if x_{i+2} != 0 then |x_{i+1}| >= p_{i+1}/2,
    # so |p_i x_{i+1}| <= |x_i| / (1 - 1/p_{i+1}); the single level below the top nonzero digit has ratio <= 2 but an
    # exact input.  Hence the relative error is <= 3u + 2(P-1)u (1 + 2^-24) <= (2P + 4) u (with slack).
    return v, (2 * P + 4) * U * 1.01


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('--workers', type=int, default=os.cpu_count())
    ap.add_argument('--tmp', default=None)
    args = ap.parse_args()
    G['t0'] = time.time()
    pkg = pickle.loads(lzma.decompress(open(args.cert, 'rb').read()))
    assert pkg['format'] == 'ep3-alld-v1'
    k, nrow = pkg['k'], pkg['nrow']
    smax = Fraction(1, pkg['d0'])
    orb = {f: E.word_orbits(k, f) for f in E.FAMILIES}
    assert sum(orb[f][1] for f in E.FAMILIES) == nrow
    blocks = [dict(kind=t['kind'], family=t['family'], rows=t['rows'], modules=t['modules'], W=t['W'])
              for t in pkg['types']]
    rx = E.Relaxation(k, blocks, pkg['diagrams'], pkg['aux'], pkg['eq_groups'], orb)
    G.update(pkg=pkg, rx=rx, ce=E.ColumnEngine(rx))
    S, R = pkg['stage2']['S'], pkg['stage2']['R']
    log('certificate: %d types, %d base equality items, stage-1 %d columns (degree %d), |S| = |R| = %d, %d rows' % (
        len(pkg['types']), len(pkg['eq_items']), len(pkg['stage1']['cols']), pkg['stage1']['q'], len(S), nrow))
    assert len(S) == len(R)
    deg_r = check_structure(pkg)
    E.check_definition(pkg)
    log('[A] multiplier classes (13 partial-transpose patterns, gram, gram2) and the five equality groups are the validated ones')
    ctx = mp.get_context('fork')
    m_ = Fraction(pkg['margin'])
    # [B]
    with ctx.Pool(args.workers) as pool:
        res = pool.map(margin_task, range(len(pkg['types'])), chunksize=4)
    nb = sum(r[1] for r in res)
    log('[B] margins: %d Bernstein coefficient blocks checked exactly, failures %d; m = %.6e' % (
        sum(r[2] for r in res), nb, float(m_)))
    assert nb == 0
    # [C]
    s1blk, s1eq = stage1_tables(pkg)
    G.update(s1blk=s1blk, s1eq=s1eq)
    q1 = pkg['stage1']['q']
    eps1 = 0.0
    for ti, lst in s1blk.items():
        for i in range(q1 + 1):
            f2 = sum(Fraction(mant[i], 2 ** ex) ** 2 * (1 if a == bb else 2) for a, bb, mant, ex in lst)
            eps1 = max(eps1, up(math.sqrt(up(f2))))
    log('[C] stage 1: sup_s ||Delta D_t(s)||_op <= eps1 = %.4e' % eps1)
    # [D] residual at NRES nodes
    assert NRES >= deg_r + pkg['W']['deg'] + 1
    G['res_nodes'] = cheb_nodes(NRES, float(smax), BRES)
    with ctx.Pool(min(args.workers, NRES)) as pool:
        out = dict(pool.imap_unordered(residual_task, range(NRES)))
    rv = [out[j][0] for j in range(NRES)]
    badr = sum(out[j][1] for j in range(NRES))
    log('[D] exact residual r\'(s) at %d nodes: max |r\'| = %.3e' % (NRES, max(max(abs(float(x)) for x in r) for r in rv)))
    log('[F] W(s)^T r\'(s) == 0 exactly at %d nodes (degree <= %d): failures %d' % (NRES, deg_r + pkg['W']['deg'], badr))
    assert badr == 0
    # [F3] rank W(1/9) mod p
    P0 = 1000003
    s0 = pow(9, -1, P0)
    rows = []
    for v in pkg['W']['vperp']:
        row = [0] * nrow
        for i, val in v['ent'].items():
            row[i] = val % P0
        rows.append(row)
    for mv in pkg['W']['moving']:
        row = [0] * nrow
        for e, coef in enumerate(mv['coef']):
            for i, val in coef.items():
                row[i] = (row[i] + val * pow(s0, e, P0)) % P0
        rows.append(row)
    rk = flint.nmod_mat(rows, P0).rank()
    log('[F] rank W(1/9) mod %d = %d (nrow - |R| = %d)' % (P0, rk, nrow - len(R)))
    assert rk == nrow - len(R)
    # height bounds and primes
    G['col_nodes'] = cheb_nodes(NCOL, float(smax), BCOL)
    Hs, Wbs = height_bounds(pkg, rx)
    need = 2 * max(H * Wb for H, Wb in zip(Hs, Wbs)) + 1
    primes, pp, prod = [], 2 ** 26, 1
    while prod <= need:
        pp -= 1
        if flint.fmpz(pp).is_prime():
            primes.append(pp)
            prod *= pp
    log('[E] height bounds: max column numerator < 2^%d, W scaling < 2^%d -> %d primes below 2^26' % (
        max(Hs).bit_length(), max(Wbs).bit_length(), len(primes)))
    G['tmp'] = args.tmp or os.path.join(os.path.dirname(os.path.abspath(args.cert)), 'tmp_alld')
    os.makedirs(G['tmp'], exist_ok=True)
    tasks = [(j, p) for j in range(NCOL) for p in primes]
    with ctx.Pool(args.workers) as pool:
        res = list(pool.imap_unordered(column_task, tasks))
    badw = sum(r[2] for r in res)
    log('[E,F] S columns at %d nodes modulo %d primes: W^T A_S nonzero in %d (node, prime) checks -> exact identity' % (
        NCOL, len(primes), badw))
    assert badw == 0
    # [G] stage 2: exact node values of A_RS (CRT) -> floats with error bounds
    scale = []
    for key in S:
        scale.append(80 + BCOL * pkg['types'][key[1]]['delta'] if key[0] == 'blk' else BCOL * k)
    scale = np.array(scale)
    An, Aerr = [], []
    for j in range(NCOL):
        # residues of the rational column values 2^80 a(s) (block) / e(s) (equality) at s = m / 2^b; multiply by
        # 2^{b delta} (resp. 2^{b k}) modulo p to get the residues of the integers N = 2^{scale} * value
        resj = []
        for p in primes:
            Rm = np.load(os.path.join(G['tmp'], 'AS_%d_%d.npy' % (j, p))).astype(np.int64)
            fac = np.array([pow(2, int(sc_) - (80 if key[0] == 'blk' else 0), p) for sc_, key in zip(scale, S)],
                           dtype=np.int64)
            resj.append((Rm * fac[None, :]) % p)
        v, rel = crt_float(resj, primes)
        A = v / (2.0 ** scale)[None, :]                                    # exact power-of-two scaling
        An.append(A)
        Aerr.append(rel * upnorm(A) * (1 + 4 * U))
        for p in primes:
            os.remove(os.path.join(G['tmp'], 'AS_%d_%d.npy' % (j, p)))
    blkmask = np.array([key[0] == 'blk' for key in S])
    mid = An[NCOL // 2]
    Dr = 2.0 ** -np.round(np.log2(np.linalg.norm(mid, axis=1)))
    Dc = 2.0 ** -np.round(np.log2(np.linalg.norm(mid, axis=0)))
    Ah = [Dr[:, None] * A * Dc[None, :] for A in An]                      # exact power-of-two scaling
    Aherr = [(Aerr[c] / upnorm(An[c])) * upnorm(Ah[c]) for c in range(NCOL)]  # entrywise relative errors are kept
    cn = [float(Fraction(x)) for x in G['col_nodes']]
    nAh = [upnorm(A) for A in Ah]

    def A_at(tq):
        w = lagrange_w(G['col_nodes'], tq)
        wf = np.array([float(x) for x in w])
        out_ = np.tensordot(wf, np.array(Ah), axes=1)
        aw = [abs(float(x)) * (1 + U) for x in w]
        err = sum(aw[c] * (Aherr[c] + (2 * U + gam(NCOL)) * nAh[c]) for c in range(NCOL)) * (1 + gam(4 * NCOL)) + 1e-280
        return out_, err
    tauB = cheb_float(QB + 1, float(smax))
    Bn = [np.linalg.inv(A_at(Fraction(float(t)))[0]) for t in tauB]
    nB = [upnorm(B) for B in Bn]
    nBblk = [upnorm(Dc[blkmask][:, None] * B[blkmask]) for B in Bn]
    tauBq = [Fraction(float(t)) for t in tauB]

    def B_at(tq):
        w = lagrange_w(tauBq, tq)
        wf = np.array([float(x) for x in w])
        out_ = np.tensordot(wf, np.array(Bn), axes=1)
        aw = [abs(float(x)) * (1 + U) for x in w]
        err = sum(aw[c] * (2 * U + gam(QB + 1)) * nB[c] for c in range(QB + 1)) * (1 + gam(4 * QB + 4)) + 1e-280
        return out_, err
    rho = len(R)
    NE = 12 + QB + 1
    tauE = cheb_float(NE, float(smax))
    emax = 0.0
    for t in tauE:
        tq = Fraction(float(t))
        Af, eA = A_at(tq)
        Bf, eB = B_at(tq)
        mid_ = Af @ Bf
        absP = np.abs(Af) @ np.abs(Bf)
        Em = np.eye(rho) - mid_
        nA_, nB_ = upnorm(Af), upnorm(Bf)
        rad = (eA * (nB_ + eB) + nA_ * eB + gam(rho) * upnorm(absP) / (1 - gam(rho))
               + U * (math.sqrt(rho) + upnorm(mid_)) + 1e-280)
        emax = max(emax, (upnorm(Em) + rad) * (1 + 4 * U))
    LE, LB, LR = lebesgue(tauE, float(smax)), lebesgue(tauB, float(smax)), lebesgue(
        np.array([float(x) for x in G['res_nodes']]), float(smax))
    theta = up(LE * emax * (1 + 4 * U))
    betab = up(LB * max(nBblk) * (1 + 4 * U))
    Rmax = 0.0
    for r in rv:
        rR = np.array([float(r[i]) for i in R])
        Rmax = max(Rmax, upnorm(Dr * rR) * (1 + 4 * U) + 4 * U * upnorm(Dr * rR))
    Rsup = up(LR * Rmax * (1 + 4 * U))
    log('[G] theta <= %.4e (max ||E(tau)||_F %.3e, Lebesgue %.3f); ||[D_c B]_blk|| <= %.4e; sup ||D_r r\'_R|| <= %.4e' % (
        theta, emax, LE, betab, Rsup))
    assert theta < 1
    eps2 = up(betab * Rsup / (1 - theta) * (1 + 8 * U))
    total = up((eps1 + math.sqrt(2) * eps2) * (1 + 8 * U))
    log('[H] eps1 + sqrt(2) eps2 <= %.4e + %.4e = %.4e  vs  m = %.6e  (ratio %.1f)' % (
        eps1, math.sqrt(2) * eps2, total, float(m_), float(m_) / total))
    ok = total < float(m_) * (1 - 4 * U)
    log('ALL-D CERTIFICATE (d >= 9): %s' % ('PASS' if ok else 'FAIL'))
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
