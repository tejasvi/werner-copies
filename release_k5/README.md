# Exact certificates for five copies of a qutrit (k = 5, d = 3) at t = 9/20 and 47/100

Self-contained: one verifier script, two certificate files, reference logs.

## Claim

For each t in {9/20, 47/100}, and for every complex 243 x 243 matrix C of rank at most 2 (C acts on
(C^3)^{x5}),

    q_5^t(C) = sum_{J subset {1,...,5}} (-t)^{|J|} ||Tr_J C||_F^2  >=  0 .

Equivalently, <psi| (I - 3t P_+)^{x5} |psi> >= 0 for every psi in (C^3 (x) C^3)^{x5} of Schmidt rank at most 2
(psi = vec C, P_+ the maximally entangled projector of one copy).  This is the 5-copy partial-transpose condition
for the qutrit Werner state with parameter alpha = -t.  The strongest statement is t = 47/100 = 0.47.  The
reduction to 5-copy undistillability for all alpha >= -t is in the accompanying paper (Corollary 2.4).

## Quick start

    python3 -m venv venv && venv/bin/pip install -r requirements.txt     # numpy, scipy, python-flint 0.9.0
    venv/bin/python -I verify_cert6.py certs/cert_k5_d3_t9_20.pkl.xz --procs 48
    venv/bin/python -I verify_cert6.py certs/cert_k5_d3_t47_100.pkl.xz --procs 48

Each run ends with `SLACK_CERTIFICATE_PASS`.  Reference outputs are in `expected/`.

| certificate | PSD blocks | primes | sum_f ‖R_f‖_1 | L K sum | nu | wall (48 procs) |
|---|---|---|---|---|---|---|
| t = 9/20 | 495, 0 failures | 13 | 4.058e-11 | 2.429e-06 | 4.575308e-03 | 7.8 min* |
| t = 47/100 | 495, 0 failures | 13 | 5.863e-14 | 3.510e-09 | 2.006286e-03 | 5.8 min |

Fresh venv (Python 3.13.5, numpy 2.5.4, scipy 1.18.1, python-flint 0.9.0) on a 96-thread x86-64 server.  \* The
server was shared with another job; the run took 5.0 min when it was otherwise idle.  The ratios nu / (L K sum) are
1.88e3 (9/20) and 5.72e5 (47/100).

## What the verifier checks

`verify_cert6.py` imports nothing from the construction code.  It checks the same claim, certificate format and
residual lemma as `verify_cert5.py` of the k = 4 package, for any k.  The moment families are
X_f = E |x_0 x_1 x_2 x_3><x_0 x_1 x_2 x_3| on four replicas of V = (C^3)^{x5} (x) C^2, with letter patterns
31 = aaab, 22 = aabb and 13 = bbba (a the isometric lifting of C, b its partner vector; both unit vectors).  They
are twirled by U(3)^5 x U(2), by site permutations and by complex conjugation.

* **Objective.**  c_t(X) = Tr[((x)_sites (I - t F_03) (x) F_03^aux) X_31] / L, with L = (2 d^k)^4 = 486^4.  On
  physical tuples (normalised by ||C||_F^2 = 1/2) c_t(X) = q_5^t(C).
* **Multipliers.**  495 blocks B = W Z W^T, W a dyadic matrix and Z an integer matrix over a power of two.  All are
  the paper's coupled Gram class (rows a a b a*, b b a b*, partial transpose on the fourth replica), typed over the
  5-site symmetry.  The verifier derives every entry literally as a partial transpose of the family that carries
  its letters.
* **Equality multipliers.**  lambda acts on the Stiefel contrasts of X31, X22, X13 and on the AAB/ABB marginals.
* **Trace multiplier.**  nu > 0.

The residual functional rho = c_t - sum_b <B_b, M_b(.)> - lambda.E - nu Tr X_31 / L is summed exactly over each
orbit of permutation words (G_f x G_f, inversion, site permutations).  At k = 5 there are 24^6 words.  The verifier
works on site-permutation classes instead: pairs (multiset of the 5 site letters, auxiliary letter), 2,358,720
points, whose orbits under G_f x G_f and inversion are exactly the word orbits (36,195 + 79,245 + 36,195).  Class
sums of a contraction are accumulated factor by factor over multisets.

**Lemma (residual bound).**  As in the k = 4 package: |rho(X)| <= K sum_f ||R_f||_1 Tr X_f with
K = prod_l ||G_l^+||_inf = (131/1440)^5 (31/180) = 1.0731e-6, where G_l is the 24 x 24 Gram matrix of the
permutation operators of factor l.  On physical tuples every block is PSD, the equalities vanish and all Tr X_f
are equal, so c_t(X) >= (nu / L - K sum_f ||R_f||_1) Tr X_31 >= 0 whenever nu >= L K sum_f ||R_f||_1
(L K = 5.987e4).

**Checks, all exact.**
1. Every Z is symmetric PSD (sign pattern of the integer characteristic polynomial).
2. The orbit sums R_f(o) are computed exactly: objective, trace and equality parts in exact integer arithmetic; the
   multiplier part block by block modulo primes p < 2^20 (float64 products, every intermediate an integer below
   2^53), recombined by the Chinese remainder theorem against a rigorous bound from the same contraction with
   absolute values.
3. The Moore-Penrose inverses are computed over Q (Penrose conditions asserted), then the final inequality is
   checked.

## Construction (record only)

- Relaxation: the paper Gram class alone at k = 5 (validity: Theorem 3.5 of the accompanying paper), in typed svec form (495 blocks,
  sum r^2 = 1,124,444, 164 GB float32).  The typed data agree with an independent direct computation at physical
  points to 2.3e-8 relative, and every block is PSD there.
- Duals: an NT-scaled primal-dual interior-point method.
  - t = 9/20: stopped at dual residual 2.3e-11 with dual value 4.575309e-3, which is
    c_5(t)/2 = (1-2t)(1-t)^4/2 = 4.5753125e-3 minus 3.5e-9, so the relaxation is tight there.
  - t = 47/100: the solver stalled near the end.  The certificate uses an iterate with dual residual 4.1e-7 and
    dual value 2.0993e-3 (the relaxation value lies in [2.1e-3, 2.9e-3]; c_5(t)/2 = 2.37e-3).
  - The relaxation is negative at t = 0.48 and 0.49: feasible primal points have objective -1.07e-4 and -1.0e-3.  So
    the threshold of this relaxation lies between 0.47 and 0.48.
- Certificates: W = dyadic(reduced basis), Z = dyadic(dual block); lambda by least squares on the point-class
  orbits.  Then refinement against the exact residual (Newton step on Z and nu, then a lambda refit).
  - t = 9/20: one round with the NT-scaled correction (PSD safety 1.00); residual 3.3e-4, then 4.1e-11.
  - t = 47/100: the NT-scaled correction would have broken PSD, so a D-scaled one (dZ = D M D) was used (PSD
    safety 0.38).  Two rounds: residual 2.2, then 7.7e-7, then 5.9e-14; nu moved from 2.0993e-3 to 2.0063e-3.

## Audit status

`verify_cert6.py` is byte-identical to the audited verifier (sha256 db8e99c0...).  The auditor's check scripts
are not part of this package.

* **t = 9/20: VERIFIED.**  The auditor checked the block type (explicit w, and the literal entry rule for 8 row pairs),
  the 5 stored equality groups (the verifier's maps against literal ones, and the stored specifications), the
  constants K_5 and L_5 with the residual lemma, and every change from the audited k = 4 verifier `verify_cert5.py`
  (the point-class orbit sums; a run on the audited k = 4 certificate reproduces it exactly).  They also re-ran the
  verifier on this file (numbers identical to `expected/verify_t9_20.log`) and tested the block decoding by an
  independent Monte Carlo that resolves the slack nu.  The k = 4 caveats C1 (the interval-extension lemma in its fixed-dimension form) and C2
  (each file needs a data audit of its stored equality specifications) apply unchanged.
* **t = 47/100: no separate audit.**  For C2, the file was compared with the audited 9/20 file.  Everything the
  verifier reads as structure is identical: the module embeddings J of the blocks and of the equalities, the
  equality specifications, and for all 495 blocks the rows, modules, flags and dyadic basis W.  Only t and the
  multiplier values (nu, Z, lambda) differ, and the verifier checks those exactly.  The auditor's check scripts also pass on
  this file: `check_eq_v6.py` (maximum error 0.0), `check_rules_v6.py` (8 row pairs, 2.9e-14) and
  `check_eq_data_full5.py` (all 5 groups valid).  These checks were run by those who constructed the certificates,
  not by the auditor; their logs are not part of this package.

## Files

    verify_cert6.py                     verifier (independent)
    requirements.txt                    numpy, scipy, python-flint 0.9.0
    certs/cert_k5_d3_t9_20.pkl.xz       t = 9/20   (22.0 MB, xz pickle)
    certs/cert_k5_d3_t47_100.pkl.xz     t = 47/100 (22.9 MB, xz pickle)
    expected/verify_t9_20.log           reference runs (fresh venv)
    expected/verify_t47_100.log
    LICENSE                             CC BY 4.0
    SHA256SUMS
