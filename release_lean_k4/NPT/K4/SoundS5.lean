/-
NPT.K4.SoundS5 — **soundness of five-family slack certificates** (five families, `d = 3`).

As `NPT.K4.soundness_slack`, for certificates whose moment families are `31`, `22`, `13`, `40` (aaaa) and `04`
(bbbb): `WF5` (25 entry rules of `ruleTab5`, five equality shapes), `IdFactS5` (classes for five families; the family
groups of 40/04 are all of `S_4`), PSD multipliers and `(2 d^k)^4 · K_k · Σ_{f<5} Σ_{j ∈ codes f} |res f j| ≤ nu` prove
`EP (Fin k) 3 (β/α)`.  The proof is that of `soundness_slack` with the five-family statements: `Xf5`, `VWc_Xf5`,
`sym_coeffs_bddG` (group `inG5 f`), `trace_Xf5`, `class_sum_res5`, `LambdaS_expand5`, `stiefel40_phys`,
`aaa_phys`, `bbb_phys`, `block_psdR` / `blockR_phys_psd5` / `blk_type_nonnegR` (record rules).
-/
import NPT.K4.SoundS
import NPT.K4.Sem5
import NPT.K4.SymB5
import NPT.K4.WF5
import NPT.K4.BlkSignR

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.K4

theorem soundness_slack5 (C : CertD) [NeZero C.d] (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α) (nu : ℚ)
    (hwf : WF5 C) (hid : IdFactS5 C α β nu)
    (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    (hslack : (2 * (C.d : ℚ) ^ C.k) ^ 4 * Kq C.k *
      ∑ f ∈ Finset.range 5, ∑ j ∈ hid.codes f, |hid.res f j| ≤ nu) :
    NPT.EP (Fin C.k) C.d ((β : ℝ) / α) := by
  intro Cop hrank
  rcases normal_form hwf.hk hwf.hd Cop hrank with h0 | ⟨A, B, hAB, ⟨cA, hcA, hA⟩, hB⟩
  · rw [h0, q_zero]
  -- transformed matrices and symmetrized physical moments
  let Aε : Bool → Matrix (Fin C.k → Fin C.d) (Fin 2) ℂ := fun ε => if ε then A.map star else A
  let Bε : Bool → Matrix (Fin C.k → Fin C.d) (Fin 2) ℂ := fun ε => if ε then B.map star else B
  let ap : Equiv.Perm (Fin C.k) × Bool → Phys.V1 C.k C.d → ℂ := fun p => Phys.vecOf (permRows p.1 (Aε p.2))
  let bp : Equiv.Perm (Fin C.k) × Bool → Phys.V1 C.k C.d → ℂ := fun p => Phys.vecOf (permRows p.1 (Bε p.2))
  let X : ℕ → Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ := fun f => ∑ p, Xf5 f (ap p) (bp p)
  have hgram : ∀ p : Equiv.Perm (Fin C.k) × Bool,
      (permRows p.1 (Aε p.2))ᴴ * permRows p.1 (Aε p.2) = (cA : ℂ) • 1 := by
    rintro ⟨σ, ε⟩
    rw [Phys.permRows_gram]
    cases ε
    · simpa [Aε] using hA
    · simp only [Aε, ↓reduceIte]
      rw [Phys.map_star_gram, hA]
      ext i j
      simp [Matrix.smul_apply, one_apply]
      split_ifs <;> simp [Complex.conj_ofReal]
  have hnsq : ∀ p : Equiv.Perm (Fin C.k) × Bool, Phys.nsq C.k C.d (ap p) = Phys.nsq C.k C.d (bp p) := by
    rintro ⟨σ, ε⟩
    simp only [ap, bp, Phys.nsq_permRows]
    cases ε
    · simp only [Aε, Bε, Bool.false_eq_true, ↓reduceIte]; rw [nsq_vecOf, nsq_vecOf, hB]
    · simp only [Aε, Bε, ↓reduceIte, Phys.nsq_map_star]; rw [nsq_vecOf, nsq_vecOf, hB]
  -- projections
  have hXproj : ∀ f, ∃ Y, IsProj (spanS (nf := nf C.k C.d) 0) (X f) Y := fun f => exists_isProj _ _
  choose Y hY using hXproj
  -- invariances of X
  have hG : ∀ f, f < 5 → ∀ g h : Fin 24, inG5 f g = true → inG5 f h = true → VWc g * X f * VWc h = X f := by
    intro f hf g h hg hh
    simp only [X, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun p _ => VWc_Xf5 hf g h hg hh _ _
  have hS : ∀ f (σ : Equiv.Perm (Fin C.k)), siteAct σ (X f) = X f := by
    intro f σ
    simp only [X, siteAct_sum, ap, bp, siteAct_Xf5, permRows_comp]
    exact Fintype.sum_equiv (Equiv.prodCongr (Equiv.mulLeft σ) (Equiv.refl Bool)) _ _ fun p => rfl
  have hT : ∀ f, (X f)ᵀ = X f := by
    intro f
    simp only [X, transpose_sum, Xf5_transpose, conjM_Xf5, ap, bp, Phys.vecOf_map_star, permRows_map_star]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Fintype.sum_bool, Fintype.sum_bool]
    simp only [Aε, Bε, Bool.false_eq_true, ↓reduceIte]
    first
      | exact add_comm _ _
      | (rw [map_star_map_star, map_star_map_star]; exact add_comm _ _)
  have hXpsd : ∀ f, (X f).PosSemidef := fun f =>
    posSemidef_sum _ fun p _ => posSemidef_vecMulVec_self_star _
  -- orbit-constant coefficients with the residual bound
  have hsym : ∀ f, f < 5 → ∃ c : (Fin (C.k + 1) → Fin 24) → ℂ, Y f = ∑ w, c w • VW (nf C.k C.d) 0 w ∧
      (∀ (g1 g2 : Fin 24) (σ : Fin C.k → Fin C.k) (ε : Bool) (w : Fin (C.k + 1) → Fin 24),
        inG5 f g1 = true → inG5 f g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w) ∧
      ∀ w, ‖c w‖ ≤ Kc C.k * ((X f).trace).re := by
    intro f hf
    obtain ⟨c₀, hc₀, hb⟩ := coeff_bound hd3 (hXpsd f) (hY f)
    exact sym_coeffs_bddG (inG5_grp hf) (hY f) (hG f hf) (hS f) (hT f) hc₀ hb
  choose! c hcY hcinv hcb using hsym
  -- traces of the moments: the same for the five families
  set T : ℝ := ∑ p : Equiv.Perm (Fin C.k) × Bool, (Phys.nsq C.k C.d (ap p)) ^ 4 with hT_def
  have htr : ∀ f, (X f).trace = (T : ℂ) := by
    intro f
    simp only [X, Matrix.trace_sum]
    rw [hT_def, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun p _ => trace_Xf5 f (ap p) (bp p) _ rfl (hnsq p).symm
  have hT0 : 0 ≤ T := by rw [hT_def]; positivity
  -- the identity fact with residuals
  have hfam : ∀ t ∈ C.types, ∀ r < t.nrows, ∀ s < t.nrows, (Sem.CertD.ruleOf t r s).fam < 5 := by
    intro t ht r hr s hs
    obtain ⟨ri, S, hS, hlt, hcut, hkp, hlp, hf5, hcons⟩ := hwf.types t ht
    exact hf5 ⟨r, hr⟩ ⟨s, hs⟩
  have hpfam : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, P.fam < 5 := by
    intro g hg P hP
    rcases hwf.eqs g hg with ⟨f, c', hfc, P', hparts, hPf, -, -⟩ | ⟨f1, c1, f2, c2, hfc, P1, P2, hparts, h1, -, h2, -, -⟩
    · rw [hparts, List.mem_singleton] at hP; subst hP; rw [hPf]; omega
    · rw [hparts] at hP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · rw [h1]; omega
      · rw [h2]; omega
  set ρ : ℂ := ∑ f ∈ Finset.range 5, ∑ j ∈ univ.image (hid.cls f), c f (hid.rep f j) * ((hid.res f j : ℚ) : ℂ)
    with hρ_def
  have hsumρ : ∑ f ∈ Finset.range 5, ∑ w, c f w * ((ΛS C α β nu f w : ℚ) : ℂ) = ρ := by
    refine Finset.sum_congr rfl fun f hf => ?_
    have hf' := Finset.mem_range.1 hf
    exact class_sum_res5 hid hf' (c f) (class_constS5 hid hf' (c f) (hcinv f hf'))
  set S : ℝ := ∑ f ∈ Finset.range 5, ∑ j ∈ hid.codes f, |((hid.res f j : ℚ) : ℝ)| with hS_def
  have hρb : ‖ρ‖ ≤ Kc C.k * T * S := by
    rw [hρ_def, hS_def, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f hf => ?_)
    have hf' := Finset.mem_range.1 hf
    have hM : ∀ w, ‖c f w‖ ≤ Kc C.k * T := by
      intro w
      have := hcb f hf' w
      rwa [htr f, Complex.ofReal_re] at this
    exact res_bound5 hid hf' (c f) hM
  rw [LambdaS_expand5 C α β nu c hfam hpfam] at hsumρ
  -- equalities vanish
  have heq : (C.eqs.map fun g => (g.parts.map fun P =>
      (P.sign : ℂ) * ∑ w, c P.fam w * ((C.eqVal g P w : ℚ) : ℂ)).sum).sum = 0 := by
    refine List.sum_eq_zero fun z hz => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hz
    rcases hwf.eqs g hg with ⟨f, c', hfc, P, hparts, hPf, hPs, hspec⟩ |
        ⟨f1, c1, f2, c2, hfc, P1, P2, hparts, hP1f, hP1s, hP2f, hP2s, hspec⟩
    · -- Stiefel
      rw [hparts]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hPs, hPf]
      have hc5 : c' < 5 := by omega
      have hf5 : f < 5 := by omega
      have hnat : [sget c' 1, sget c' 2, sget c' 3] = natOrder (sget c' 0) := by
        rcases hfc with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
      have hXst : applyG (stKer (nf := nf C.k C.d) (fun l : Fin (C.k + 1) => ¬ l.val < C.k) c') (X f) = 0 := by
        simp only [X, applyG_sum, stKer_eq_stF]
        refine Finset.sum_eq_zero fun p _ => ?_
        rcases hfc with ⟨hf013, rfl⟩ | ⟨rfl, rfl⟩
        · rw [csl_cord_0.1, csl_cord_0.2]
          rcases hf013 with rfl | rfl | rfl
          · rw [Xf5_lt3 (show (0 : ℕ) < 3 by norm_num)]
            exact Phys.stiefel31_phys _ cA (hgram p) _
          · rw [Xf5_lt3 (show (1 : ℕ) < 3 by norm_num)]
            exact Phys.stiefel22_phys _ cA (hgram p) _
          · exact stiefel40_phys _ cA (hgram p) _
        · rw [csl_cord_1.1, csl_cord_1.2, Xf5_lt3 (show (2 : ℕ) < 3 by norm_num)]
          exact Phys.stiefel13_phys _ cA (hgram p) _
      have hYst := stiefel_proj (slotTab_ok ⟨c', hc5⟩) (fun p => trTab_ok ⟨c', hc5⟩ p)
        (fun q t => embTab_ok ⟨c', hc5⟩ q t) (fun l : Fin (C.k + 1) => ¬ l.val < C.k) (hY f) hXst
      rw [hcY f hf5] at hYst
      have := eq_stief_link C g P hc5 hnat (fun l => (P.specs.getD l.val default).mkeys)
        (fun l => hspec l) (by have := hwf.hd; omega) (c f) hYst
      rw [this]; simp
    · -- marginal
      rw [hparts]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hP1s, hP2s, hP1f, hP2f]
      have hc1 : c1 < 5 := by omega
      have hc2 : c2 < 5 := by omega
      have hf1 : f1 < 5 := by omega
      have hf2 : f2 < 5 := by omega
      have hXm : applyG (trKer (nf := nf C.k C.d) c1) (X f1) = applyG (trKer (nf := nf C.k C.d) c2) (X f2) := by
        simp only [X, applyG_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rcases hfc with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · show applyG (fun _ => delK (csl 2) (cord 2)) _ = applyG (fun _ => delK (csl 2) (cord 2)) _
          rw [csl_cord_2.1, csl_cord_2.2, Xf5_lt3 (show (0 : ℕ) < 3 by norm_num),
            Xf5_lt3 (show (1 : ℕ) < 3 by norm_num)]
          exact Phys.aab_phys _ _ (hnsq p)
        · show applyG (fun _ => delK (csl 3) (cord 3)) _ = applyG (fun _ => delK (csl 4) (cord 4)) _
          rw [csl_cord_3.1, csl_cord_3.2, csl_cord_4.1, csl_cord_4.2, Xf5_lt3 (show (1 : ℕ) < 3 by norm_num),
            Xf5_lt3 (show (2 : ℕ) < 3 by norm_num)]
          exact Phys.abb_phys _ _ (hnsq p)
        · show applyG (fun _ => delK (csl 1) (cord 1)) _ = applyG (fun _ => delK (csl 1) (cord 1)) _
          rw [csl_cord_1.1, csl_cord_1.2]
          exact aaa_phys _ _ (hnsq p)
        · show applyG (fun _ => delK (csl 1) (cord 1)) _ = applyG (fun _ => delK (csl 1) (cord 1)) _
          rw [csl_cord_1.1, csl_cord_1.2]
          exact bbb_phys _ _ (hnsq p)
      have hYm := marginal_proj (slotTab_ok ⟨c1, hc1⟩) (slotTab_ok ⟨c2, hc2⟩) (fun p => trTab_ok ⟨c1, hc1⟩ p)
        (fun p => trTab_ok ⟨c2, hc2⟩ p) (fun q t => embTab_ok ⟨c1, hc1⟩ q t) (fun q t => embTab_ok ⟨c2, hc2⟩ q t)
        (hY f1) (hY f2) hXm
      rw [hcY f1 hf1, hcY f2 hf2] at hYm
      have := eq_marg_link C g P1 P2 hc1 hc2 (fun l => (P1.specs.getD l.val default).mkeys)
        (fun l => (hspec l).1) (fun l => (hspec l).2) (by have := hwf.hd; omega) (c f1) (c f2) hYm
      rw [this]; push_cast; ring
  -- blocks are nonnegative
  have hblk : 0 ≤ (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
      ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum := by
    refine List.sum_nonneg fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
    obtain ⟨ri, S, hSc, hlt, hcut, hkp, hlp, hf5, hcons⟩ := hwf.types t ht
    let fam : Fin t.nrows → Fin t.nrows → ℕ := fun r s => (Sem.CertD.ruleOf t r.val s.val).fam
    let rr : Fin t.nrows → Fin t.nrows → RuleRec := fun r s => rule5 (ri r s)
    have hok : ∀ r s, (rr r s).OK := fun r s => rules5_ok ⟨ri r s, hlt r s⟩
    have hXb : (blockR rr fam X).PosSemidef := by
      simp only [X]
      rw [blockR_sum]
      exact posSemidef_sum _ fun p _ => blockR_phys_psd5 t rr fam hok hcons _ _
    have hYb := block_psdR hSc rr fam hok hcut hY hXb
    have hnn := blk_type_nonnegR C t rr fam hkp hlp Y hYb (hpsd t ht)
    have e : ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
        ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ) =
        ∑ r : Fin t.nrows, ∑ s : Fin t.nrows, C.blkOp t r.val s.val (Y (fam r s)) := by
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [C.sum_blk, hcY _ (hf5 r s)]
    rw [e]; exact hnn
  -- the objective and the trace term
  have hobj : ∑ w, c 0 w * ((objT C α β w : ℚ) : ℂ) =
      (OobjT C.k C.d α β * X 0).trace / ((α : ℂ) ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4) := by
    rw [sum_objT, ← hcY 0 (by norm_num), trace_OobjT_proj _ _ (hY 0)]
  have htrY : ∑ w, c 0 w * ((trW C w : ℚ) : ℂ) = (T : ℂ) := by
    rw [sum_trW, ← hcY 0 (by norm_num), trace_proj (hY 0), htr 0]
  have hα0 : (α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  set r0 : ℝ := (Phys.nsq C.k C.d (Phys.vecOf A)) ^ 2 * (α : ℝ) ^ C.k * NPT.q ((β : ℝ) / α) (A * Bᴴ) with hr0
  have hTX : (OobjT C.k C.d α β * X 0).trace = ((2 * C.k.factorial * r0 : ℝ) : ℂ) := by
    simp only [X, Matrix.mul_sum, Matrix.trace_sum, ap, bp, Xf5_lt3 (show (0 : ℕ) < 3 by norm_num)]
    have e1 : ∀ p : Equiv.Perm (Fin C.k) × Bool,
        (OobjT C.k C.d α β * Phys.Xf 0 (Phys.vecOf (permRows p.1 (Aε p.2)))
          (Phys.vecOf (permRows p.1 (Bε p.2)))).trace =
        (OobjT C.k C.d α β * Phys.Xf 0 (Phys.vecOf (Aε p.2)) (Phys.vecOf (Bε p.2))).trace := by
      intro p
      rw [← Phys.siteAct_Xf, trace_OobjT_siteAct]
    simp only [e1]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    rw [Fintype.sum_bool]
    have hT0' : (OobjT C.k C.d α β * Phys.Xf 0 (Phys.vecOf A) (Phys.vecOf B)).trace = ((r0 : ℝ) : ℂ) :=
      obj_physT _ _ hα0 A B
    have hT1 : (OobjT C.k C.d α β * Phys.Xf 0 (Phys.vecOf (A.map star)) (Phys.vecOf (B.map star))).trace =
        ((r0 : ℝ) : ℂ) := by
      rw [← Phys.vecOf_map_star, ← Phys.vecOf_map_star, ← Phys.conjM_Xf, trace_OobjT_conjM, hT0',
        Complex.star_def, Complex.conj_ofReal]
    simp only [Aε, Bε, ite_true, ite_false, Bool.false_eq_true, hT0', hT1]
    push_cast
    ring
  -- conclusion: objective − nu tr X / L − ρ = blocks ≥ 0
  have hfin : ∑ w, c 0 w * ((objT C α β w : ℚ) : ℂ) - (nu : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 * (T : ℂ) - ρ =
      (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
        ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum := by
    rw [htrY, heq, sub_zero] at hsumρ
    linear_combination hsumρ
  rw [← hfin, hobj, hTX] at hblk
  have hcast : ((2 * C.k.factorial * r0 : ℝ) : ℂ) / ((α : ℂ) ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4)
      - (nu : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 * (T : ℂ) =
      (((2 * C.k.factorial * r0) / ((α : ℝ) ^ C.k * (2 * (C.d : ℝ) ^ C.k) ^ 4)
        - (nu : ℝ) / (2 * (C.d : ℝ) ^ C.k) ^ 4 * T : ℝ) : ℂ) := by
    push_cast; ring
  rw [hcast] at hblk
  have hre : 0 ≤ (2 * C.k.factorial * r0) / ((α : ℝ) ^ C.k * (2 * (C.d : ℝ) ^ C.k) ^ 4)
      - (nu : ℝ) / (2 * (C.d : ℝ) ^ C.k) ^ 4 * T - ρ.re := by
    have := (Complex.le_def.1 hblk).1
    rw [Complex.zero_re, Complex.sub_re, Complex.ofReal_re] at this
    linarith
  -- the slack dominates the residual
  have hd0 : (0 : ℝ) < C.d := by have := hwf.hd; exact_mod_cast (by omega : 0 < C.d)
  have hL : (0 : ℝ) < (2 * (C.d : ℝ) ^ C.k) ^ 4 := by positivity
  have hsl : (2 * (C.d : ℝ) ^ C.k) ^ 4 * Kc C.k * S ≤ (nu : ℝ) := by
    rw [← Kq_cast, hS_def]
    exact_mod_cast hslack
  have hKS : Kc C.k * S ≤ (nu : ℝ) / (2 * (C.d : ℝ) ^ C.k) ^ 4 := by
    rw [le_div_iff₀ hL]; linarith
  have hρre : -(Kc C.k * T * S) ≤ ρ.re := by
    have h1 : |ρ.re| ≤ ‖ρ‖ := Complex.abs_re_le_norm ρ
    have h2 := neg_abs_le ρ.re
    linarith
  have hkey : Kc C.k * T * S ≤ (nu : ℝ) / (2 * (C.d : ℝ) ^ C.k) ^ 4 * T := by
    have := mul_le_mul_of_nonneg_right hKS hT0
    linarith
  have hreal : 0 ≤ (2 * C.k.factorial * r0) / ((α : ℝ) ^ C.k * (2 * (C.d : ℝ) ^ C.k) ^ 4) := by linarith
  -- positivity of the prefactors
  have hN : (0 : ℝ) < (α : ℝ) ^ C.k * (2 * (C.d : ℝ) ^ C.k) ^ 4 := by
    have : (0 : ℝ) < α := by exact_mod_cast hα
    positivity
  have h1 : 0 ≤ 2 * C.k.factorial * r0 := by
    have := mul_nonneg hreal hN.le
    rwa [div_mul_cancel₀ _ hN.ne'] at this
  have hfac : (0 : ℝ) < 2 * C.k.factorial := by positivity
  have hr0nn : 0 ≤ r0 := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hnpos : 0 < Phys.nsq C.k C.d (Phys.vecOf A) := by
    rw [nsq_vecOf, gram_trace A cA hA]; linarith
  have h2k : (0 : ℝ) < (Phys.nsq C.k C.d (Phys.vecOf A)) ^ 2 * (α : ℝ) ^ C.k := by
    have : (0 : ℝ) < α := by exact_mod_cast hα
    positivity
  rw [hAB]
  by_contra hq
  push Not at hq
  have : r0 < 0 := by rw [hr0]; exact mul_neg_of_pos_of_neg h2k hq
  linarith

end NPT.K4

#print axioms NPT.K4.soundness_slack5
