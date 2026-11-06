# Soundness of the moment certificates in Lean, without Haar measure or Schur–Weyl (design note)

Goal: `EP (Fin k) d (1/2)` from a certificate that passes the verifier checks of the published release.

(Sections 0–2 are the original design, written for the verifier of the two-copy (k = 2) certificates; the
implementation follows the k = 3 verifier `ep3core.py`, whose structure is the same. Section 3 describes what was built.)

## 0. Notation (matches the k = 2 verifier)

- **Local factors:** l ∈ L = Fin (k+1). The k "sites" have n_l = d; the auxiliary qubit (the last factor) has n_l = 2.
- **The space V:** V = ⊗_l C^{n_l}. There are four replicas r ∈ Fin 4.
- **Global index (factor-major):** i : (l : L) → (Fin 4 → Fin (n l)). Replica r of factor l carries digit i l r.
- **Local words:** p ∈ S_4. V_p acts on (C^n)^{⊗4} and sends tensor factor r to p r: (V_p)_{tgt,src} = [∀ r, tgt (p r) = src r].
- **Global words:** w = (p_l)_l, with V_w = ⊗_l V_{p_l} (entries are products over factors).
- **Partial transpose:** Γ_S on replica slots S (per factor) swaps row and column digits at the slots in S.
- **Maps used by the coupled Gram block:**
  - 'A' (per factor): Y ↦ (V_τ Y V_τ)^{Γ_{3}}, with τ = (0 1 3 2);
  - 'B' (gram_cross): B(Y)[i0 i1 i2 i3; j0 j1 j2 j3] = Y[i0 i1 i2 j3; i3 j2 j0 j1].
  - Both are entrywise index permutations, so they are Hilbert–Schmidt isometries.
- **Physical point:** a, b ∈ V with a = Σ_r |r⟩_aux ⊗ x_r, b = Σ_r |r⟩_aux ⊗ y_r, C = Σ_r x_r y_r^*. Normalisation: Tr_{sites}|a⟩⟨a| = I_2/2 (Stiefel) and ‖b‖ = 1.
- **Physical moments:** w31 = a⊗a⊗a⊗b, w22 = a⊗a⊗b⊗b, w13 = a⊗b⊗b⊗b (replica order 0..3), and X_f = |w_f⟩⟨w_f|.
- **The certificate functional on operators Y_f:**
  - c(Y31) = Tr(O·Y31) / (2^k (2 d^k)^4), with O = ⊗_{sites}(2I − F_{03}) ⊗ F_{03}^{aux};
  - minus Σ_t ⟨B_t, J_t^T Y_{f_t}^{Γ_t} J_t⟩ (src blocks), or, for a gram block, ⟨B11, J^T A(Y31) J⟩ + 2⟨B12, J^T B(Y22) J⟩ + ⟨B22, J^T A(Y13) J⟩;
  - minus λ·E(Y).
  - Here J_t = ⊗_l J_{t,l} (integer module matrices) and B_t = W_t Z_t W_t^T / (zden · Wden²).
- **What the verifier checks:**
  - (C1) for every family f and every orbit O of words under G_f × G_f × site permutations × inversion, Σ_{w∈O} Λ_f(V_w) = 0;
  - (C2) every Z_t is PSD.

## 1. The Haar-free argument

The key step is to replace the twirl by the Hilbert–Schmidt orthogonal projection P onto a unital *-subalgebra. Define, per factor and globally:

- A = span{V_w}. It is unital and closed under products (V_w V_u = V_{wu}) and under adjoint (V_w^* = V_{w^{-1}}).
- A_Γ := Γ(A) = span{V_w^Γ}, for each cut pattern Γ used by a src block. It is a *-subalgebra: the walled Brauer algebra. The closure needs only finitely many structure constants per local n and cut.
- A' := 'A'(A) = 'B'(A) for the gram class. This needs checking: both maps send A onto the same *-algebra (the Γ_3 Brauer algebra after τ). M_2 ⊗ A' is then a *-algebra.

**Lemma P (positivity of the conditional expectation).** Let 𝒜 ⊆ M_m(ℂ) be a unital *-subalgebra. Let Z ∈ 𝒜 satisfy Tr(Y^* Z) = Tr(Y^* X) for all Y ∈ 𝒜. If X ⪰ 0, then Z ⪰ 0.

*Proof.*
1. Z is Hermitian, because 𝒜 is *-closed and X is Hermitian.
2. Let Z_− be the negative part of Z, Z_− = p(Z) for a polynomial p interpolating max(−x, 0) on spec Z. Then Z_− ∈ 𝒜 and Z_− ⪰ 0.
3. On one hand, Tr(Z_− Z) = Tr(Z_− X) ≥ 0. On the other, Tr(Z_− Z) = −Tr(Z_−²) ≤ 0.
4. So Z_− = 0. ∎

No Haar measure and no Schur–Weyl are needed. The facts used are Mathlib spectral calculus, polynomial interpolation on a finite set, and the trace of a product of PSD matrices being ≥ 0.

**Lemma I (intertwining).** Let T : M → M' be linear with T(𝒜) ⊆ 𝒜′ and T^*(𝒜′) ⊆ 𝒜. Then T ∘ P_𝒜 = P_{𝒜′} ∘ T. This applies to:
- Γ, 'A' and 'B' (HS isometries mapping A onto the target algebra);
- partial traces and identity embeddings, which map 4-replica words to 3-replica words and back;
- the Stiefel map 2·id − I⊗Tr on the aux factor;
- conjugation by V_g, for replica relabelling.

**Main chain** for a physical point (a, b):
- (M1) Symmetrise. Average the moment data over the finite group S_k (site permutations) × {id, complex conjugation} acting on (a, b). Each image is again a physical point with the same q, because q is invariant under copy permutation and under C ↦ C̄.
- (M2) Y_f := average of P(X_f(g·(a, b))). Then Y_f ∈ A. Y_f is also invariant under:
  - G_f relabelling (V_g X_f = X_f = X_f V_h);
  - site permutations;
  - inversion (Hermitian with real coefficients after the conjugation average).
  So Y_f = Σ_w x_w V_w with x constant on orbits (average any representation over the finite group). By (C1), Λ(Y) = 0.
- (M3) c(Y31) = q(C)/(2d^k)^4. The reasons:
  - O ∈ A, so Tr(O·P(X)) = Tr(O X);
  - the swap identity ⟨a⊗b|F_aux ⊗ F_S|a⊗b⟩ = ‖Tr_S C‖²;
  - Tr(Pa) = ‖a‖² = 1.
- (M4) Block terms ≥ 0:
  - src: J^T P(X)^Γ J = J^T P_{A_Γ}(X^Γ) J ⪰ 0, since X^Γ = |w^Γ⟩⟨w^Γ| (conjugated slots) and by Lemma P;
  - gram: the 2×2 block equals P_{M_2⊗A'} of the Gram matrix of (a a b ā) ⊕ (b b a b̄), which is ⪰ 0;
  - then ⟨B_t, M⟩ = ⟨Z_t, W^T M W⟩ ≥ 0 for M ⪰ 0 and Z_t ⪰ 0.
- (M5) E(Y) = 0. E(X) = 0 holds as an operator identity for physical X:
  - the Stiefel identity Tr_sites|a⟩⟨a| = I/2;
  - the marginals: tracing an a-slot of X31 gives the same as tracing an a-slot of X22, and similarly for abb.
  Then E∘P = P'∘E (Lemma I).
- (M6) q(C)/(2d^k)^4 = c(Y31) = Σ_t (block terms) + λ·E(Y) ≥ 0.
- (M7) Reduction to the physical normal form: every rank-≤2 C ≠ 0 is a positive multiple of a normalised physical C (Gram–Schmidt on the two left vectors), and q is homogeneous of degree 2.

## 2. Lean work breakdown

| # | Item | Size | Notes |
|---|---|---|---|
| 1 | Lemma P (general, Matrix m m ℂ) | M | CFC or Lagrange interpolation; PSD trace product |
| 2 | Lemma I (general linear algebra) | S | finite-dimensional; P characterised by the trace equations |
| 3 | Global word algebra: entries as products over factors; V_w V_u = V_{wu}; adjoint | M | `Finset.prod_univ_sum` |
| 4 | Γ-algebras A_Γ, the 'A'/'B' images: product closure | L | structure constants per n ∈ {2,3} and cut (finite: decide/native), or a general-n Brauer-diagram lemma (kernel, reusable for all d) |
| 5 | Physical moments and their Γ/A/B images as Gram matrices | M | index bookkeeping |
| 6 | Objective via the swap identity, against `NPT.ptrace`/`frobSq` | M–L | |
| 7 | Stiefel/marginal identities for physical X; E∘P = P'∘E | M | |
| 8 | Symmetrisation; orbit-constant coefficients; invariance of q | M | |
| 9 | Certificate semantics: Λ_f(V_w) as a Lean function of the data, plus the checker link | L | the checker must evaluate exactly this function, or prove equal |
| 10 | Normal form (M7) | S–M | |

S = small, M = medium, L = large. Estimate: about 3–5k lines of Lean in total. The general items (1, 2, 3, 6, 7, 8, 10) carry over to k = 3 unchanged. Item 4 is the only n-specific mathematics, and item 9 is the data.

## 3. As implemented (2026-10-24, all compiled; std axioms [propext, Classical.choice, Quot.sound]; no sorry)

Final interface: `NPT.Cert.soundness_of_check (C : Sem.CertD) [NeZero C.d] (hwf : wfCheck C = true) (hid : Sem.IdFact C)
(hpsd : ∀ b ∈ C.Z, (b.Zmat C.Lden).PosSemidef) : EP (Fin C.k) C.d (1/2)` (NPT/Cert/WFCheck.lean); d = 3 instance
`NPT.Cert.EP3_d3_of_idFact` (NPT/Cert/EP3_d3.lean) with `EP3D3.wf_cert` (kernel, 12 s) and `blocks_psd`.

Module map (import order):
| module | content |
|---|---|
| CondExp | Lemma P (`condexp_posSemidef`, CFC negative part) |
| Brauer, BrauerTab, BrauerData | selection operators `SelOp`, `GCert` reparametrisation (`GCert.csum_eq`), VG = partially transposed V_p, product tables for the 7 cuts (decide +kernel, generic in n) |
| Glob | `kron` calculus, global words `VW`, star algebras `AS S` (walled Brauer), `blockAlg` |
| Proj | HS projection `IsProj` (exists/unique/linear), intertwining `IsProj.map`, `map_eq_zero` |
| Rules, RuleData | entry-rule maps `ruleL/ruleG` (HS unitary), 13 verified rules V_p ↦ VG cut q (decide +kernel) |
| Sem | semantic target (CertD, Λ, IdFact; ep3core semantics) — the interface between soundness and the per-d checks |
| Phys, PhysObj, PhysEq, PhysStiefel, PhysSym | physical vectors, X_f, objective identity, marginal/Stiefel identities, symmetry invariances |
| BlockPos | `block_psd` (Lemma P on blockAlg (AS S)), `phys_rule` (physical blocks are Gram) |
| EqMaps, EqLocal, EqData, EqInt | product-kernel maps, partial trace / Stiefel kernels, closed forms (decide), `marginal_proj`, `stiefel_proj` |
| SymDefs, Sym | site/conj/word actions; `sym_coeffs` (orbit-constant coefficients of the projection) |
| SemLink, BlkSign, EqLink, Assembly | Sem ↔ operators (blk_eq/sum_blk, obj_eq/sum_obj, eq links), type sign `blk_type_nonneg`, `class_sum_zero`, `Lambda_expand` |
| NormalForm, SoundPrep, Soundness | normal form; `soundness` (WF + IdFact + PSD ⇒ EP) |
| WFCheck, WFd3, EP3_d3 | computable `wfCheck` + soundness; d = 3 instance |
