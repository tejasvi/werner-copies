# Exact certificates for four copies of a qutrit (k = 4, d = 3) at t = 49/100, 99/200, 62/125, 497/1000, 2489/5000 and 4979/10000

Self-contained: one verifier script, six certificate files, reference logs.

## Claim

For each t in {49/100, 99/200, 62/125, 497/1000, 2489/5000, 4979/10000}, and for every complex 81 x 81 matrix C of
rank at most 2
(C acts on (C^3)^{x4}),

    q_4^t(C) = sum_{J subset {1,2,3,4}} (-t)^{|J|} ||Tr_J C||_F^2  >=  0 .

Equivalently, <psi| (I - 3t P_+)^{x4} |psi> >= 0 for every psi in (C^3 (x) C^3)^{x4} of Schmidt rank at
most 2 (psi = vec C, P_+ the maximally entangled projector of one copy).  This is the 4-copy partial-transpose
condition for the qutrit Werner state with parameter alpha = -t.  The reduction to undistillability for all
alpha >= -t is in the accompanying paper (Corollary 2.4).

## Quick start

    python3 -m venv venv && venv/bin/pip install -r requirements.txt     # numpy, python-flint 0.9.0
    venv/bin/python -I verify_cert5.py certs/cert_k4_d3_t49_100.pkl.xz --procs 24
    venv/bin/python -I verify_cert5.py certs/cert_k4_d3_t99_200.pkl.xz --procs 24
    venv/bin/python -I verify_cert5.py certs/cert_k4_d3_t62_125.pkl.xz --procs 24
    venv/bin/python -I verify_cert5.py certs/cert_k4_d3_t497_1000.pkl.xz --procs 24
    venv/bin/python -I verify_cert5.py certs/cert_k4_d3_t2489_5000.pkl.xz --procs 24
    venv/bin/python -I verify_cert5.py certs/cert_k4_d3_t4979_10000.pkl.xz --procs 24

Each run ends with `SLACK_CERTIFICATE_PASS`.  Reference outputs are in `expected/`.

| certificate | PSD blocks | primes | sum_f ‖R_f‖_1 | L K sum | nu | wall (24 procs) | max RSS |
|---|---|---|---|---|---|---|---|
| t = 49/100 | 3816, 0 failures | 13 | 4.806e-13 | 3.905e-09 | 1.326504e-03 | 4.9 min | 2.3 GB |
| t = 99/200 | 3816, 0 failures | 13 | 2.838e-16 | 2.306e-12 | 4.885624e-04 | 5.0 min | 2.3 GB |
| t = 62/125 | 3816, 0 failures | 13 | 2.193e-15 | 1.782e-11 | 3.524339e-04 | 6.2 min* | 2.3 GB |
| t = 497/1000 | 3816, 0 failures | 13 | 2.754e-16 | 2.238e-12 | 5.962708e-06 | 5.2 min* | 2.3 GB |
| t = 2489/5000 (FULL5) | 4893, 0 failures | 14 | 3.437e-17 | 2.792e-13 | 4.608278e-05 | 9.5 min | 4.5 GB |
| t = 4979/10000 (FULL5) | 4893, 0 failures | 14 | 2.289e-16 | 1.859e-12 | 1.148082e-05 | 7.3 min | 4.6 GB |

The times are from a fresh venv (Python 3.13, numpy 2.5.4, python-flint 0.9.0) on a shared 384-thread x86-64 server
(* = construction venv, same versions).  The strongest statement is t = 4979/10000 = 0.4979.
- The first four certificates use the relaxation base + paper Gram + Gram class 2.  Its value is about +7.55e-6
  at t = 0.497 and -2.84e-4 at t = 0.4975, so its threshold is about 0.49701.
- The certificates at 2489/5000 and 4979/10000 use the complete degree-4 relaxation (FULL5).  FULL5 adds the
  families X40, X04 and the Gram classes c3s2, c3s0 and c23s0.  Its value is +7.279e-5 at t = 0.4978, about
  +1.60e-5 at t = 0.4979 and -4.16e-5 at t = 0.498, so its threshold is about 0.49793.

## What the verifier checks

`verify_cert5.py` imports nothing from the construction code.  It uses the four-replica moment relaxation
(after Zenodo 23134454).  The moment families are X_f = E |x_0 x_1 x_2 x_3><x_0 x_1 x_2 x_3| on four replicas
of V = (C^3)^{x4} (x) C^2, with letter patterns 31 = aaab, 22 = aabb and 13 = bbba.  Here a is the isometric
lifting of C and b its partner vector; both are unit vectors.  The FULL5 certificates (2489/5000, 4979/10000)
also use 40 = aaaa and 04 = bbbb.  The families are twirled by U(3)^4 x U(2), by site permutations and by complex
conjugation.

* **Objective.**  c_t(X) = Tr[((x)_sites (I - t F_03) (x) F_03^aux) X_31] / L, with L = (2 d^k)^4.  On physical
  tuples (normalised by ||C||_F^2 = 1/2) c_t(X) = q_4^t(C); in general c_t(X) is a positive multiple of q_4^t(C).
* **Multipliers.**  Each block is B = W Z W^T, with W a dyadic matrix and Z an integer matrix over a power of
  two.  Its rows are letter patterns with conjugation flags.  The verifier derives the entry |u_r><u_s| of a
  block literally as a partial transpose of the family that carries its letters, using permutation
  operators, partial traces and module embeddings J (integer data).  Three kinds of block occur in all six
  certificates: whole-replica partial transposes (all cuts), the paper's coupled Gram block, and the second
  Gram class.  The FULL5 certificates add more:
  * the whole-replica blocks of X40 and X04 (cut ());
  * the Gram class c3s2, rows a a a a* / a a b b*;
  * the Gram class c3s0, rows b b b b* / a b b a*;
  * the three-row Gram class c23s0, rows a a a* a* / b b b* b* / a b a* b*.
* **Equality multipliers.**  lambda acts on the Stiefel contrasts of X31, X22, X13 and on the AAB/ABB marginals.
  The FULL5 certificates add the Stiefel contrast of X40 and the AAA/BBB marginals:
  Tr_3 X31 = Tr_3 X40 and Tr_3 X13 = Tr_3 X04.
* **Trace multiplier.**  nu >= 0.

The residual functional is

    rho = c_t - sum_b <B_b, M_b(.)> - lambda.E - nu Tr X_31 / L ,

and R_f(o) denotes its exact sum over each orbit o of permutation words (G_f x G_f, inversion, site
permutations).

**Lemma (residual bound).**  A twirled X_f lies in span{V_w}.  Its Moore-Penrose coefficients x = G^+ g, with
g_v = Tr(V_v^* X_f), are constant on the orbits.  Their size is bounded by |x_w| <= K Tr X_f, where
K = prod_l ||G_l^+||_inf and G_l is the 24 x 24 Gram matrix of the permutation operators of factor l.  This
follows because |Tr(V_v^* X_f)| <= Tr X_f for X_f >= 0.  Hence |rho(X)| <= K sum_f ||R_f||_1 Tr X_f.

On physical tuples every block is PSD, the equalities vanish, and all Tr X_f are equal.  Therefore

    c_t(X) >= (nu / L - K sum_f ||R_f||_1) Tr X_31 >= 0    whenever    nu >= L K sum_f ||R_f||_1 ,

and c_t(X) is a positive multiple of q_4^t(C).

The exact constants are ||G^+||_inf = 131/1440 at n = 3 (rank 23) and 31/180 at n = 2 (rank 14), so
L K = 162^4 (131/1440)^4 (31/180), about 8.12e3.

**Checks, all exact.**
1. Every Z is symmetric PSD (sign pattern of the integer characteristic polynomial).
2. The orbit sums R_f(o) are computed exactly, over 6892 + 14837 + 6892 orbits (plus 683 + 683 for X40 and X04):
   * objective, trace and equality parts in exact integer arithmetic;
   * the multiplier part block by block modulo primes p < 2^20 (float64 products, every intermediate an integer
     below 2^53), recombined by the Chinese remainder theorem against a rigorous bound from the same
     contraction with absolute values.
3. The Moore-Penrose inverses are computed over Q (Penrose conditions asserted), then the final inequality is
   checked.

## Construction (record only)

The multipliers come from an interior-point solution of the relaxation:
- base + paper Gram + Gram class 2, which has value 1.32651e-3 at t = 0.49, 6.43938e-4 at t = 0.495 and about
  7.55e-6 at t = 0.497;
- FULL5 for 2489/5000 and 4979/10000.  Its data are typed float32 (4893 blocks, total dimension 50697).  The
  solver was stopped at an interior point of the central path so that the dual is well conditioned:
  mu 5.4e-10 with dual value 4.608e-5 (2489/5000), and mu 9.0e-11 with dual value 1.148e-5 (4979/10000).
The construction scripts are not part of this package.  The steps are:
1. Write the multipliers in the solver's reduced coordinates (W = dyadic basis, Z = dual block).
2. Fit lambda by least squares in orbit space.
3. Refine against the exact residual: map it to variable space, solve on the well-conditioned eigen-directions
   of Z so that PSD is preserved, then refit lambda.  This is done once (twice for the FULL5 certificates).

## Audit status

`verify_cert5.py` is byte-identical to the audited verifier (sha256 a907b423...).  The auditor's check
scripts were written for the audit and do not use the construction code; they are not part of this package.

* **t = 49/100: VERIFIED.**  The auditor checked that the 15 row sets give valid multipliers (explicit vectors w), the
  residual lemma and the constant K, and the 5 stored equality groups (by hand and by code).  They re-ran an unmodified
  copy of the verifier (numbers identical to `expected/verify_t49_100.log`), confirmed that the verifier rejects a
  copy with nu multiplied by 10, and tested the block decoding by an independent Monte Carlo on twirled physical
  points.  They also checked the reduction to 4-copy undistillability for all alpha >= -0.49, which this package does
  not contain.  Two caveats remain.  C1: the interval-extension lemma is used in its
  fixed-dimension form (d = 3), which is how the accompanying paper states it (Lemma 2.3(b)).  C2: the verifier reads
  the equality specifications from the certificate file, so every file needs this data audit.
* **t = 2489/5000: VERIFIED.**  A follow-up audit of this file covered the five FULL5 block types (explicit w and
  the literal entry rule for all 80 row pairs), the 8 stored equality groups and the slack constant, and included a
  verifier re-run (numbers identical to `expected/verify_t2489_5000.log`) and a Monte Carlo test on the file.  C1 and C2 apply
  unchanged.
* **t = 99/200, 62/125, 497/1000 and 4979/10000: no separate audit.**  For C2, each file was compared with the audited
  file of the same relaxation (49/100 for the first three, 2489/5000 for 4979/10000).  Everything the verifier reads as
  structure is identical: the module embeddings J of the blocks and of the equalities, the equality specifications,
  and for every block its rows, modules, flags and dyadic basis W.  Only t and the multiplier values (nu, Z, lambda)
  differ, and the verifier checks those exactly.  The auditor's `check_eq.py` (the verifier's equality maps against
  literal ones) gives maximum error 0.0 on all four files.  On 4979/10000 the literal rule check (80 row pairs) and
  the auditor's specification check (`check_eq_data_full5.py`: all 8 groups valid) also pass.  These checks were run
  by those who constructed the certificates, not by the auditor; their scripts and logs are not part of this package.

## Inventory

Each certificate is byte-identical to the construction output.

| file | sha256 (first 16) | MB | relaxation | blocks / eq. groups | nu / (L K sum) | audit |
|---|---|---|---|---|---|---|
| certs/cert_k4_d3_t49_100.pkl.xz | 5e3d3b1c4434bd00 | 12.4 | base + paper Gram + Gram class 2 | 3816 / 5 | 3.397e5 | VERIFIED |
| certs/cert_k4_d3_t99_200.pkl.xz | f1b333570a16451b | 11.9 | base + paper Gram + Gram class 2 | 3816 / 5 | 2.119e8 | structure = 49/100 |
| certs/cert_k4_d3_t62_125.pkl.xz | 703c77dfea40ab90 | 11.5 | base + paper Gram + Gram class 2 | 3816 / 5 | 1.978e7 | structure = 49/100 |
| certs/cert_k4_d3_t497_1000.pkl.xz | 137c1dc29eb83752 | 11.8 | base + paper Gram + Gram class 2 | 3816 / 5 | 2.665e6 | structure = 49/100 |
| certs/cert_k4_d3_t2489_5000.pkl.xz | 331c0d1a5e5bdb0a | 35.0 | FULL5 | 4893 / 8 | 1.650e8 | VERIFIED |
| certs/cert_k4_d3_t4979_10000.pkl.xz | dce9c7ec07ccae19 | 34.4 | FULL5 | 4893 / 8 | 6.174e6 | structure = 2489/5000 |

The other files are `verify_cert5.py` (the audited verifier), `requirements.txt`, one reference log per certificate in
`expected/` (62/125 and 497/1000 from the construction venv, the others from a fresh venv), `LICENSE` and `SHA256SUMS`
(full hashes of every file).  The command lines that `time -v` recorded in the logs were shortened to relative
paths.  The companion package `release_k5` holds the k = 5, d = 3 certificates at t = 9/20 and 47/100 with their
verifier `verify_cert6.py`.

## Files

    verify_cert5.py                     verifier (independent)
    requirements.txt                    numpy, python-flint 0.9.0
    certs/cert_k4_d3_t49_100.pkl.xz     t = 49/100   (12.4 MB, xz pickle)
    certs/cert_k4_d3_t99_200.pkl.xz     t = 99/200   (11.9 MB)
    certs/cert_k4_d3_t62_125.pkl.xz     t = 62/125   (11.5 MB)
    certs/cert_k4_d3_t497_1000.pkl.xz   t = 497/1000 (11.8 MB)
    certs/cert_k4_d3_t2489_5000.pkl.xz  t = 2489/5000 (35.0 MB, FULL5 relaxation)
    certs/cert_k4_d3_t4979_10000.pkl.xz t = 4979/10000 (34.4 MB, FULL5 relaxation)
    expected/verify_t49_100.log         reference runs
    expected/verify_t99_200.log
    expected/verify_t62_125.log
    expected/verify_t497_1000.log
    expected/verify_t2489_5000.log
    expected/verify_t4979_10000.log
    LICENSE                             CC BY 4.0
    SHA256SUMS
