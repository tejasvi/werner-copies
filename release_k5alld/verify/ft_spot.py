"""Check of the per-site polynomial data (uni/ftpoly.pkl): for every cut and label, FT_poly(n) = sum_i coef[i] n^i
must equal the exact local Fourier data M_nu[p] = G_nu pi_nu(p) = J^T V_p^Gamma J of local.module_data(4, cut, n)
(rows flattened (i, j), columns P4) at n = 4, 5, 6.  Usage: ft_spot.py"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import k5defs as KD

if KD.ZM not in sys.path:
    sys.path.insert(0, KD.ZM)
from local import module_data

FTP = KD.load_ftp()
for n in (4, 5, 6):
    for cut, P in FTP.items():
        data = module_data(4, tuple(sorted(cut)), n)
        labs = list(data)
        assert [tuple(l) for l in labs] == [tuple(l) for l in P['labels']], ('label order', cut, n)
        coef = np.asarray(P['coef'], dtype=object)
        bad = 0
        for li, l in enumerate(labs):
            d = data[l]['dim']
            assert d == P['dims'][li]
            rows = range(P['off'][li], P['off'][li + 1])
            for a, pi in enumerate(data[l]['pi']):
                Mx = data[l]['G'] * pi
                for i in range(d):
                    for j in range(d):
                        r = P['off'][li] + i * d + j
                        val = sum(int(coef[e, r, a]) * n ** e for e in range(coef.shape[0]))
                        if val != int(Mx[i, j]):
                            bad += 1
        print('n = %d cut %-7s: %d labels, mismatches %d' % (n, cut, len(labs), bad), flush=True)
        assert bad == 0
print('FT_poly(n) == G pi (module_data) for all cuts, labels, p at n = 4, 5, 6')
