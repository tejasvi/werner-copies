"""Word-level orbit labels of S_4^5 x S_4 (24^6 = 191,102,976 words per family) under
    H_f = S_5 (site permutations)  x  L_f,   L_f = {sigma -> g sigma h, sigma -> g sigma^-1 h : g, h in G_f}
(L_f acts letterwise on all 6 letters, sites and ancilla alike).

Own implementation, on WORDS (no multiset/class reduction): min-label propagation with pointer jumping over the
generator maps (adjacent site transpositions, left and right multiplication by the transpositions of G_f, inversion;
all involutions, so the graph is undirected).  Verified by:
  (i)   every generator map preserves the labels;
  (ii)  the number of labels equals the Burnside count of H_f orbits (computed from fixed-point counts of all |H_f|
        elements), so every label class is exactly one H_f orbit;
  (iii) every orbit size divides |H_f|.
Usage: orbits_words.py OUTDIR [families]      writes OUTDIR/oid_<f>.npy (int64, orbit index per word) and sizes_<f>.npy
"""
import os, sys, time, itertools, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from k5defs import K, NW, NWORD, P4, I4, FAMS, GF, TRANSP, LMUL, RMUL, INV, compose, inverse

t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
OUT = sys.argv[1]
fams = sys.argv[2].split(',') if len(sys.argv) > 2 else list(FAMS)
os.makedirs(OUT, exist_ok=True)
NPOS = K + 1
POW = [NW ** (NPOS - 1 - i) for i in range(NPOS)]          # digit i (site i; i = 5 the ancilla) has weight 24^(5-i)

idx = np.arange(NWORD, dtype=np.int64)
D = np.empty((NPOS, NWORD), dtype=np.uint8)
for i in range(NPOS):
    D[i] = (idx // POW[i]) % NW
del idx
log('digits built')


def encode(digs):
    acc = np.zeros(NWORD, dtype=np.int64)
    for i in range(NPOS):
        acc *= NW
        acc += digs[i]
    assert acc.max() < 2 ** 31
    return acc.astype(np.int32)


def burnside(f):
    """number of H_f orbits on words, from fixed-point counts of all elements (pi, phi) of S_5 x L_f"""
    maps = set()
    for g in GF[f]:
        for h in GF[f]:
            maps.add(tuple(I4[compose(compose(g, p), h)] for p in P4))
            maps.add(tuple(I4[compose(compose(g, inverse(p)), h)] for p in P4))
    maps = [np.array(m) for m in maps]
    total = 0
    for pi in itertools.permutations(range(K)):
        seen, cyc = set(), []
        for i in range(K):
            if i not in seen:
                c, j = 0, i
                while j not in seen:
                    seen.add(j); j = pi[j]; c += 1
                cyc.append(c)
        for m in maps:
            pw = {}                                          # number of letters fixed by phi^c
            def pmap(c):
                if c not in pw:
                    a = np.arange(24)
                    for _ in range(c):
                        a = m[a]
                    pw[c] = int(np.sum(a == np.arange(24)))
                return pw[c]
            prod = pmap(1)                                   # ancilla letter: fixed by pi
            for c in cyc:
                prod *= pmap(c)
            total += prod
    order = math.factorial(K) * len(maps)
    assert total % order == 0
    return total // order, order, len(maps)


for f in fams:
    gens, names = [], []
    for i in range(K - 1):                                    # adjacent site transpositions (ancilla untouched)
        digs = list(D); digs[i], digs[i + 1] = D[i + 1], D[i]
        gens.append(encode(digs)); names.append('site(%d,%d)' % (i, i + 1))
    for g in TRANSP[f]:
        gens.append(encode([LMUL[g][D[i]] for i in range(NPOS)])); names.append('L%s' % (g,))
        gens.append(encode([RMUL[g][D[i]] for i in range(NPOS)])); names.append('R%s' % (g,))
    gens.append(encode([INV[D[i]] for i in range(NPOS)])); names.append('inv')
    for gm in gens:                                           # involutions -> undirected graph
        assert np.array_equal(gm[gm], np.arange(NWORD, dtype=np.int32))
    log('family %s: %d generator maps %s' % (f, len(gens), names))
    lab = np.arange(NWORD, dtype=np.int32)
    it = 0
    while True:
        it += 1
        old = lab.copy()
        for gm in gens:
            np.minimum(lab, lab[gm], out=lab)
        while True:                                           # pointer jumping
            nl = lab[lab]
            if np.array_equal(nl, lab):
                break
            lab = nl
        ch = int(np.count_nonzero(lab != old))
        log('  pass %d: %d labels changed' % (it, ch))
        if ch == 0:
            break
    for gm, nm in zip(gens, names):
        assert np.array_equal(lab[gm], lab), ('generator not label-preserving', nm)
    uniq, oid = np.unique(lab, return_inverse=True)
    norb = len(uniq)
    oid = oid.astype(np.int64).reshape(-1)
    sizes = np.bincount(oid, minlength=norb)
    nb, order, nmaps = burnside(f)
    assert norb == nb, ('orbit count differs from Burnside', norb, nb)
    assert np.all(order % sizes == 0), 'orbit size does not divide |H_f|'
    np.save(os.path.join(OUT, 'oid_%s.npy' % f), oid)
    np.save(os.path.join(OUT, 'sizes_%s.npy' % f), sizes)
    log('family %s: %d orbits (Burnside %d, |L_f| = %d, |H_f| = %d), max size %d, min size %d; saved' % (
        f, norb, nb, nmaps, order, sizes.max(), sizes.min()))
    del gens, lab, oid, sizes, uniq
