"""Export a run_exact certificate to the self-contained format read by verify_cert.py."""
import pickle
import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, '<ROOT>/dim')
from local import module_data, label_name
from exact_cert import W_of


def full_J(m, cut, n, lab):
    data = module_data(m, tuple(sorted(cut)), n)[lab]
    J = data['J']
    out = np.zeros((n ** m, J.shape[1]), dtype=object)
    for i, x in enumerate(data['basis']):
        idx = 0
        for t in x:
            idx = idx * n + t
        for c in range(J.shape[1]):
            out[idx, c] = int(J[i, c])
    return out


def key(n, cut, lab):
    return '%d|%s|%s' % (n, ','.join(map(str, cut)), label_name(lab))


def main():
    src = pickle.load(open(sys.argv[1], 'rb'))
    outp = sys.argv[2]
    k, d = src['k'], src['d']
    modules = {}
    blocks = []
    for t, Nl, Z in zip(src['types'], src['N'], src['Z']):
        cut = t['cut']
        labs_s = list(module_data(4, tuple(sorted(cut)), d))
        labs_a = list(module_data(4, tuple(sorted(cut)), 2))
        mods = []
        for i in t['st']:
            kk = key(d, cut, labs_s[i])
            if kk not in modules:
                modules[kk] = full_J(4, cut, d, labs_s[i]).tolist()
            mods.append(kk)
        kk = key(2, cut, labs_a[t['ai']])
        if kk not in modules:
            modules[kk] = full_J(4, cut, 2, labs_a[t['ai']]).tolist()
        mods.append(kk)
        W = W_of(t, Nl)
        blocks.append(dict(kind=t['kind'], family=t['f'], modules=mods, W=W.tolist(), Wden=1, Z=Z))
    # equality modules and groups
    eq_modules = {}

    def eqkeys(m, n):
        labs = list(module_data(m, (), n))
        ks = []
        for lab in labs:
            kk = 'eq%d|%d|%s' % (m, n, label_name(lab))
            eq_modules[kk] = full_J(m, (), n, lab).tolist()
            ks.append(kk)
        return ks

    s3 = eqkeys(3, d)
    a3 = eqkeys(3, 2)
    a4 = eqkeys(4, 2)
    names = ['stiefel31', 'stiefel22', 'stiefel13', 'aab', 'abb']
    lam = {name: [] for name in names}
    for (g, o), v in zip(src['lam_index'], [src['lam'][str(kk)] for kk in src['lam_index']]):
        lam[names[g]].append((list(o), v))
    groups = {}
    for f, slot, name in (('31', 0, 'stiefel31'), ('22', 0, 'stiefel22'), ('13', 3, 'stiefel13')):
        nat = tuple(i for i in range(4) if i != slot)
        loc = [(d, slot, nat, 'del', s3)] * k + [(2, slot, nat, 'stiefel_aux', a4)]
        groups[name] = dict(lambda_=None, parts=[dict(family=f, sign=1, local=loc)])
    for name, (f1, s1, o1), (f2, s2, o2) in (('aab', ('31', 2, (0, 1, 3)), ('22', 2, (0, 1, 3))),
                                              ('abb', ('22', 1, (0, 2, 3)), ('13', 1, (3, 0, 2)))):
        p1 = dict(family=f1, sign=1, local=[(d, s1, o1, 'del', s3)] * k + [(2, s1, o1, 'del', a3)])
        p2 = dict(family=f2, sign=-1, local=[(d, s2, o2, 'del', s3)] * k + [(2, s2, o2, 'del', a3)])
        groups[name] = dict(parts=[p1, p2])
    for name in names:
        groups[name]['lambda'] = lam[name]
        groups[name].pop('lambda_', None)
    cert = dict(k=k, d=d, blocks=blocks, modules=modules, eq_modules=eq_modules, eq_groups=groups,
                lam={str(kk): v for kk, v in src['lam'].items()},
                note='q_k endpoint certificate; see verify_cert.py for the checked claim')
    pickle.dump(cert, open(outp, 'wb'))
    print('exported', len(blocks), 'blocks,', len(modules), 'modules ->', outp)


if __name__ == '__main__':
    main()
