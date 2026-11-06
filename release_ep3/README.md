# EP_3 for every local dimension d ≥ 3 — compact certificate and standalone verifier

This directory proves, by a computer check that runs on a laptop in well under an hour, that the four-replica moment
relaxation of the three-copy endpoint problem has value 0 for every local dimension d ≥ 3. With the validity of the
relaxation (Theorem 3.5 of the accompanying paper) this gives EP_3 for every d ≥ 3. Explicitly: for every complex d³ × d³ matrix C of rank ≤ 2,

    q_3(C) = Σ_{J ⊆ [3]} (−1/2)^{|J|} ‖Tr_J C‖_F² ≥ 0.

Two certificates cover all d:

| dimensions | certificate | verifier | what the verifier checks |
|---|---|---|---|
| d = 3, …, 8 | `certs/ep3_perd_dD.pkl.xz` (0.21–0.32 MB each) | `verify_perd.py` | completes a low-height certificate to an exact one, then checks the exact identity on all 4675 word orbits and exact PSD of every multiplier |
| every d ≥ 9 | `certs/ep3_alld.pkl.xz` (9.97 MB) | `verify_alld.py` | one polynomial certificate in s = 1/d on [0, 1/9], plus a two-stage exact-correction argument with rigorous bounds (Lemma RA below) |

Total size is 11.7 MB; the data it was built from take 45 GB.

## Quick start

    python3 -m venv .venv
    .venv/bin/pip install -r requirements.txt        # numpy >= 2, python-flint == 0.9.0
    PYTHON=.venv/bin/python ./run_all.sh 8           # 8 = worker processes

`run_all.sh` does three things:
1. checks `SHA256SUMS`;
2. runs the six per-d verifications, three at a time;
3. runs the all-d verifier.

It ends with `EP_3 VERIFIED FOR EVERY d >= 3`. Logs go to `logs/`, and a reference run is in `expected/`.

Reference timings (8 workers, Python 3.13.5, numpy 2.5.4, python-flint 0.9.0):

| step | wall time | peak memory |
|---|---|---|
| per-d, d = 3…8 (three at a time) | 9.8 min (3.0–5.2 min per d) | about 2 GB per process |
| all-d (`verify_alld.py`) | 23.2 min | 5.8 GB |
| **total (`run_all.sh 8`)** | **33.1 min** | |

The reference machine was a shared 384-thread x86-64 server at load ~120, with 8 workers and one BLAS thread per process. On an
otherwise idle 8-core machine the all-d step took 19.6 min. The CPU time for everything is about 2.8 h.

## Independence

The verifier is `ep3core.py`, `verify_perd.py` and `verify_alld.py`, about 1,500 lines in total. It imports only
numpy, python-flint and the Python standard library. It implements the relaxation from its definition:
- letter patterns of the moment families X31, X22, X13 and the coupled Gram classes;
- literal index rules of the entries |u_r⟩⟨u_s| with partial transposes;
- permutation operators, partial traces and Stiefel contrasts;
- the closed-form objective;
- **diagram compressions** of the site modules (see below).

Nothing is imported from the code that constructed the certificates. That code is kept in `prover/` for the record
only. It needs the 45 GB of construction data and is **not** needed for verification.

`check_definition` in `ep3core.py` pins the relaxation to the validated classes. The allowed multipliers are:
- single-row whole-replica partial transposes of a family's moment operator;
- the `gram` class (rows `a a b a*`, `b b a b*`);
- the `gram2` class (rows `a a a* b*`, `a b b* b*`).

The allowed equality functionals are the five canonical groups: Stiefel contrasts at the a-replicas, and the AAB and
ABB marginals. Certificate data cannot change any of this.

## Mathematical structure

**Site modules as diagram compressions.** Fix one site, i.e. four replica slots of C^n, and a cut (the conjugated
slots). For each label (f, λ, μ), the module basis is J(n) = D(n) C. Here C is a fixed integer matrix with entries in
{−1, 0, 1}. Each column of D(n) is a diagram vector

    D_key(n) = Σ_{j ∈ [n]^f} e_x,

where:
- x = j on f contraction pairs (non-cut slot, cut slot);
- the other non-cut slots carry the "top" values 0, 1, …;
- the other cut slots carry the "bottom" values n−1, n−2, ….

For a partially transposed permutation operator O, the entry ⟨D_a|O|D_b⟩ is computed by **loop counting**. The
operator's matching, together with the pair edges, splits into free cycles (a factor n each) and paths between two
fixed values (a factor [values equal]). Top and bottom values never coincide for n ≥ 4: a collision needs
n = t + r + 1 ≤ 3, which is asserted. At n = 3 the exact rule is applied; for the labels that exist at n = 3, collisions
cannot occur. So every local map is Σ_c M_c n^c with c ≤ 2f.

Two facts follow:
- *(validity)* any compression K†MK of a PSD operator is PSD, so the relaxation defined with these modules is a valid
  relaxation at every n (the argument of Theorem 3.5; no rank or isometry condition is needed);
- *(polynomiality)* after the scaling s^{δ_t}, with δ_t = 2·Σ f over the sites, every verifier column, the objective
  and every residual is a polynomial in s = 1/n of known degree.

The verifier asserts the standard diagram keys, integer C, c ≤ 2f and δ_t = 2Σf. These are the inputs of the
data-polynomiality lemma; given them, every degree claim holds by construction.

**d ≥ 9 (Lemma RA, two-stage form).** Notation:
- A(s) is the s-scaled verifier map in conditioned block coordinates D_t, with Z_t = s^{δ_t} T_r D_t T_r^T and
  T_r = T/2^40 integral;
- x_P(s) is the base certificate: rounded Bernstein blocks of degree p_t ≤ 12 − δ_t, and equality polynomials of
  degree 9.

The verifier checks:

- **[B] margins.** C_{t,j} − m T_r T_r^T ⪰ 0 for all 13,233 Bernstein coefficient blocks, exactly, with
  m = 2.71224·10⁻⁶. Hence Z_t(s)/s^{δ_t} ⪰ m T_r T_r^T on [0, 1/9].
- **[C] stage 1.** An explicit degree-20 polynomial correction Δx(s), stored as 41-bit dyadic Bernstein coefficients.
  Its block part satisfies ‖ΔD_t(s)‖ ≤ ε₁ = 1.88·10⁻⁹.
- **[D] residual.** r'(s) = c − A(s)(x_P + Δx), computed exactly at 38 nodes; its degree is ≤ 32. Measured
  max |r'| = 3.9·10⁻¹⁹.
- **[E] stage-2 columns.** A_S(s), the columns of a square subset S (2634 coordinates), at 18 nodes modulo 15 primes.
  The number of primes comes from an a-priori height bound. Each column has degree ≤ 12.
- **[F] consistency.** A left-kernel witness W(s) satisfies the checks below. It consists of 1934 constant sparse
  vectors plus 107 integral vectors of degree ≤ 5 with entries below 2^63, LLL-reduced. The rank bound itself is free,
  because |S| = 2634.
  - W^T A_S ≡ 0, exact by the height bound over 18 nodes (degree ≤ 17);
  - W^T r' ≡ 0, exact at 38 nodes (degree ≤ 37);
  - rank W(1/9) = 4675 − 2634.
- **[G] Neumann bound.** The verifier computes approximate inverses B(s) of the normalised A_RS(s) itself, by
  interpolating at 21 Chebyshev points. It shows θ = sup‖I − A_RS B‖ < 1 with rigorous midpoint-radius bounds and
  Lebesgue constants (θ ≤ 1.22·10⁻⁵), and bounds the stage-2 block correction by ε₂.
- **[H]** ε₁ + √2 ε₂ < m. Reference run: ε₁ = 1.88·10⁻⁹ and √2 ε₂ = 5.16·10⁻⁹, total 7.04·10⁻⁹ < 2.712·10⁻⁶, a
  factor of 385.

Conclusion, for every s ∈ [0, 1/9]:
1. θ < 1 gives rank A_RS(s) = 2634. W gives generic rank A_S ≤ 2634, so the rank is 2634 everywhere and the rows R
   span the row space of A_S.
2. r'(s) is in the range of A_S(s). W spans the left kernel at all but finitely many s, and the range projector is
   continuous at constant rank.
3. δ(s) = B(I − E)^{-1} r'_R(s) therefore solves the identity in **all** rows.
4. Every block stays ⪰ (m − ε₁ − √2ε₂) I ≻ 0.

At s = 1/d every quantity is rational, so this is an exact certificate of the diagram relaxation at d.

**d = 3, …, 8.** Each file holds:
- the exact per-d certificate rounded to about 120 significant bits (dyadic);
- a square set S of raw coordinates (equality items first, then raw Gram entries) and a row set R.

The verifier then:
1. computes the residual exactly;
2. computes the exact S columns at d (CRT);
3. solves A_RS u = r_R exactly;
4. checks the completed certificate: the identity is exact on every one of the 4675 word orbits, and every multiplier
   is PSD by the exact characteristic polynomial.

Step 4 alone is the proof.

## Files

| file | content |
|---|---|
| `ep3core.py` | the relaxation in closed form: orbits, entry rules, diagram loop counting, contraction, columns modulo primes |
| `verify_alld.py` | all-d verifier, d ≥ 9 |
| `verify_perd.py` | per-d verifier, d = 3…8 |
| `run_all.sh` | runs everything |
| `requirements.txt` | numpy, python-flint 0.9.0 |
| `certs/` | the seven certificates (xz-compressed pickles of plain Python ints, strings, tuples, lists, dicts) |
| `expected/` | logs of the reference run |
| `prover/` | construction scripts, for the record only (not needed; they need the construction data) |
| `LICENSE` | CC BY 4.0 |
| `SHA256SUMS` | sha256 of every file above |

## Notes

- The certificates are pickles of plain built-in types; no classes are unpickled. Load them only from this trusted
  package.
- python-flint 0.9.0 provides exact integer and rational matrices (fmpz_mat, fmpq_mat), modular rank (nmod_mat)
  and exact characteristic polynomials.
- The per-d and all-d verifications are independent. Each can be run alone:
  `python3 verify_perd.py certs/ep3_perd_d5.pkl.xz` or `python3 verify_alld.py certs/ep3_alld.pkl.xz --workers 8`.
