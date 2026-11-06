# Four-copy Werner undistillability for α ≥ −79/160 in every dimension: exact verification package

**Theorem (Theorem 1.3 of the accompanying paper).** For every local dimension d ≥ 2 and every α ≥ −79/160 = −0.49375, the Werner state
ρ(d, α) = (I + αF)/(d² + αd) is 4-copy undistillable.

Equivalently, for every complex matrix C on (C^d)^{⊗4} of rank at most two and every t ∈ [0, 79/160],

    q₄(t, C) = Σ_{J ⊆ {1,2,3,4}} (−t)^{|J|} ‖Tr_J C‖²_F ≥ 0.

By Costa Rico's criterion (Lett. Math. Phys. 115:47, 2025), the two statements are equivalent. For α > 0 every term of q₄(−α, ·) is nonnegative.

This directory reproduces the computer-assisted part of the proof in exact rational arithmetic, end to end, from the certificate. Theorem numbers below refer to the accompanying paper.

## Quick start

    python3 -m venv .venv && .venv/bin/pip install -r requirements.txt     # numpy >= 2, scipy, sympy, python-flint 0.9.0
    PYTHON=.venv/bin/python ./run_all.sh 16                                 # 16 = parallel exact-worker jobs

The run ends with `K4 EXACT CHECK PASSED`. Logs go to `logs/` and regenerated intermediates to `work/`. Reference outputs are in `expected/`.

Optional switches:
- `REFIT_LAMBDA=1` re-derives the equality multipliers (see step 3).
- `RUN_E2E=1` runs a physical-point sanity check.
- `RUN_FLOAT=1` runs the original floating-point verifier as a cross-check.

## Proof structure

1. **Dimension monotonicity (paper, Lemma 2.3(a)).** If q₄(t, ·) ≥ 0 on rank-≤2 matrices in dimension D, the same holds in every d ≤ D, because zero padding by an isometry ι preserves rank and every ‖Tr_J C‖. Hence it suffices to prove q₄(79/160, ·) ≥ 0 for every d ≥ d₀ = 1.25·10⁹.
2. **t monotonicity (paper, Lemma 2.3(b)).** If q_j(t, ·) ≥ 0 for all j ≤ 4, then q₄(t′, ·) ≥ 0 for all 0 ≤ t′ ≤ t. Moreover, q₄(t, ·) ≥ 0 implies q_j(t, ·) ≥ 0 for j < 4.
3. **Slack form (paper, Lemma 3.6), applied at each fixed n ≥ 4.** Fix PSD multipliers Q_t = M_t M_t^T on the raw typed spaces, equality multipliers λ, and ν = 1/10000. Then for every rank-2 C, with X its symmetrized four-replica moment tuple,

       c(X) ≥ (ν − LK(n) Σ_o |R(o; 1/n)|) τ(X),   LK(n) = 16 (n⁴‖G_site(n)^{-1}‖_∞)⁴ ‖G_aux⁺‖_∞,

   where R(o; s) is the orbit sum of the word-level residual. The inequality uses that every raw typed block is PSD on physical tuples and every equality row vanishes there; this validity of the k-site relaxation is paper Theorem 3.5.
4. **Residual bound (paper, Section 6).** Every word residual is a polynomial in s = 1/n:

       ρ(w; s) = R0(w) + s R1(w) + (terms of degree ≥ 2),

   and for 0 ≤ s ≤ s₀,

       Σ_o |R(o; s)| ≤ S0 + s S1 + s² S2.

   For n ≥ 1.25·10⁹:

   | quantity | value |
   |---|---|
   | S0 = Σ_o \|R0(o)\| | 8.799734e-7 (exact) |
   | S1 = Σ_o \|R1(o)\| | 8221.293 (exact) |
   | S2 | ≤ 8.0883e9 (absolute shadow) |
   | LK | ≤ 2.7555556 |
   | margin ν − LK(S0 + s₀S1 + s₀²S2) | **7.94e-5 > 0** |

   Steps 1–4 together prove the theorem.

## What each script checks (run_all.sh)

| step | script | content |
|---|---|---|
| 0 | `sha256sum -c SHA256SUMS` | integrity of every shipped file |
| 1 | `verify/lk_exact.py` | exact ‖G_aux⁺‖_∞ = 31/180 (rank 14), the Neumann bound for G_site(n), and LK(1.25e9) = 2.7555556 |
| 2 | `verify/prep_m.py` | builds the multiplier factors M_t = C_t·chol(D_t + μI) from the certificate; Q_t = M_t M_t^T is PSD by construction, for any real M_t |
| 3 | `verify/prep_eq.py` | equality structure (Stiefel contrasts at the a-slots, marginal pairings) and the multipliers λ (`certs/lambda_t79_160.npy`) |
| 4 | `verify/orbits.py` | orbit labels of S₄⁵ under the symmetry group; counts 6892 / 14837 / 6892 |
| 5 | `verify/s2_bound.py` | rigorous upper bound on S2 (full absolute shadow, no subtraction, ×1.01) |
| 6 | `verify/exact_worker.py` | exact residues mod p of the orbit sums of R0 and R1, for 18 primes p < 2²⁰ and 3 key-chunks each |
| 7 | `verify/combine.py` | CRT over 17 primes (340 bits), checked against the 18th; exact S0 and S1 as rationals with denominator 2^261·5⁴; the margin |
| 8 (optional) | `verify/e2e_check.py` | physical rank-2 points at n = 4, 50, 1000, 1.25e9: the objective reproduces q₄, the trace reproduces Tr X, the coefficient bound holds, all equality rows vanish, and every src block term is ≥ 0 |
| 9 (optional) | `crosscheck/word_rig_v2.py` | the original floating-point verifier, with a-priori rounding bounds (margin 4.54e-5) |

Notes on steps 3 and 6:
- **λ.** The shipped λ was derived from the certificate: least squares of the raw s = 0 equality rows against EtT_nu − μ·tr. Any λ is admissible, because equality rows vanish on physical tuples, and the exact check verifies whichever λ is used.
- **Rounding in step 6.** The exact check applies fixed-point rounding, each step of which keeps the certificate valid: M and λ are rounded to 2^-60, and the float equality left factors to 2^-40 (any common left factor of a vanishing contrast is admissible). The trace multiplier is exactly ν = 1/10000.
- **Arithmetic in step 6.** Residues are held in float64, and every product and partial sum stays below 2⁵³, so the BLAS contractions are exact.

## Validity

The computation proves the margin inequality for this certificate. Validity of each ingredient is proved in the accompanying paper:
- every raw typed block of the k-site relaxation is PSD, and every equality row vanishes, on physical tuples (Theorem 3.5);
- zero padding and t-monotonicity (Lemma 2.3);
- the slack form (Lemma 3.6);
- this certificate and its residual bound (Section 6).

The per-site data `data/ftpoly.pkl` are the exact polynomial-in-n local data. Every entry is 0 or n^{#loops} for n ≥ 4, so the degree in n is at most 2f.

Index convention: the X13 replica pattern is (b, b, b, a), with a in slot 3.

## Compute requirements (measured reference run)

- **Exact check (`./run_all.sh 54`):** 54 exact-worker jobs, all running concurrently on a recent x86-64 server shared with other work.
  - Each job took 11.5–16 min (median 14.3 min).
  - The whole run took 18.5 min wall time and 12.9 CPU-hours.
  - Each job used about 0.9 GB of memory; no step used more than 3.9 GB.
- **With fewer parallel jobs:** with N jobs the exact step takes about 54/N × 14 min. Use N ≈ number of cores, and about 1 GB of RAM per job.
- **Optional steps:**
  - `REFIT_LAMBDA=1` adds about 12 min and needs about 25 GB of RAM;
  - `RUN_FLOAT=1` adds about 15 min.

Per-job times are in `expected/worker_times.txt`.

## Contents

- `certs/`:
  - `ipm_s0_gp_t79_160.pkl`: the certificate (sha256 9c4fda05…dc43);
  - `exact_types_k4_d4.pkl`, `ns_ident_k4.pkl`: typed spaces and ranges;
  - `lambda_t79_160.npy`: equality multipliers;
  - `meta_*_slim.pkl`: the only fields of the original meta files that are used (γ, tr₃₁, t).
- `data/ftpoly.pkl`: per-site polynomial data (sha256 559789929b…50c2).
- `zm/`: the relaxation's index-convention, local-Fourier and equality-row modules (`relax.py`, `local.py`, `exact.py`, `exact_blocks.py`), copied unchanged from the code that produced the certificate.
- `verify/`: the exact verifier.
- `crosscheck/word_rig_v2.py`: the floating-point verifier that accompanied the certificate. Only its module path and its loader of `data/ftpoly.pkl` differ from the original, whose sha256 is 2a1c7ba8cd6e187f9b48f8f993d4ca467769c3a5a1f3bc3d0fc0be9a7ea3f39c.
- `expected/`: reference outputs of `run_all.sh` and of the optional checks.
- `LICENSE`: CC-BY-4.0.
- `SHA256SUMS`: every shipped file.

## Caveats

- The relaxation data (typed spaces, ranges, local Fourier data) are taken from the computation that produced the certificate. Their validity is the content of paper Theorem 3.5, not re-derived here.
- The physical-point sanity check (step 8) uses product points only. The exact residual computation covers every word.
