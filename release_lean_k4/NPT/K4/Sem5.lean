/-
NPT.K4.Sem5 — the identity fact with claimed residuals for five families, and the five-family expansion of the
paired slack identity (five-family certificate).

`ΛS` (`NPT.K4.SemS`) is already generic in the family index.  `IdFactS5` is `IdFactS` with `f < 5` and the family
groups `inG5` (all of `S_4` for 40/04); `class_sum_res5` / `res_bound5` are `class_sum_res` / `res_bound` for it, and
`LambdaS_expand5` is `LambdaS_expand` summed over the five families.
-/
import NPT.K4.SemS
import NPT.K4.Phys5

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem

namespace NPT.K4

/-- **The identity fact with claimed residuals, five families.** -/
structure IdFactS5 (C : CertD) (α β : ℕ) (nu : ℚ) where
  cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ
  rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24)
  wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool
  hG : ∀ f < 5, ∀ w, inG5 f (wit f w).1 = true ∧ inG5 f (wit f w).2.1 = true
  hσ : ∀ f < 5, ∀ w, Function.Bijective (wit f w).2.2.1
  hrep : ∀ f < 5, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w)
  res : ℕ → ℕ → ℚ
  codes : ℕ → Finset ℕ
  hcodes : ∀ f < 5, ∀ w, cls f w ∈ codes f
  hsum : ∀ f < 5, ∀ w₀, ∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ΛS C α β nu f w = res f (cls f w₀)

section IdFactS5

variable {C : CertD} {α β : ℕ} {nu : ℚ}

lemma class_constS5 (hid : IdFactS5 C α β nu) {f : ℕ} (hf : f < 5) (c : (Fin (C.k + 1) → Fin 24) → ℂ)
    (hinv : ∀ (g1 g2 : Fin 24) (σ : Fin C.k → Fin C.k) (ε : Bool) (w : Fin (C.k + 1) → Fin 24),
      inG5 f g1 = true → inG5 f g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w)
    (w : Fin (C.k + 1) → Fin 24) : c w = c (hid.rep f (hid.cls f w)) := by
  rw [← hid.hrep f hf w]
  exact (hinv _ _ _ _ w (hid.hG f hf w).1 (hid.hG f hf w).2 (hid.hσ f hf w)).symm

lemma class_sum_res5 (hid : IdFactS5 C α β nu) {f : ℕ} (hf : f < 5) (c : (Fin (C.k + 1) → Fin 24) → ℂ)
    (hc : ∀ w, c w = c (hid.rep f (hid.cls f w))) :
    ∑ w, c w * ((ΛS C α β nu f w : ℚ) : ℂ) =
      ∑ j ∈ univ.image (hid.cls f), c (hid.rep f j) * ((hid.res f j : ℚ) : ℂ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (hid.cls f))
    (g := hid.cls f) (fun w _ => Finset.mem_image_of_mem _ (Finset.mem_univ w))]
  refine Finset.sum_congr rfl fun v hv => ?_
  obtain ⟨w₀, -, hw₀⟩ := Finset.mem_image.1 hv
  have e : ∀ w ∈ Finset.univ.filter (fun w => hid.cls f w = v),
      c w * ((ΛS C α β nu f w : ℚ) : ℂ) = c (hid.rep f v) * ((ΛS C α β nu f w : ℚ) : ℂ) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [hc w, hw.2]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have h0 := hid.hsum f hf w₀
  rw [hw₀] at h0
  rw [← Rat.cast_sum, h0]

lemma res_bound5 (hid : IdFactS5 C α β nu) {f : ℕ} (hf : f < 5) (c : (Fin (C.k + 1) → Fin 24) → ℂ) {M : ℝ}
    (hM : ∀ w, ‖c w‖ ≤ M) :
    ‖∑ j ∈ univ.image (hid.cls f), c (hid.rep f j) * ((hid.res f j : ℚ) : ℂ)‖ ≤
      M * ∑ j ∈ hid.codes f, |((hid.res f j : ℚ) : ℝ)| := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM fun _ => 0)
  have hsub : univ.image (hid.cls f) ⊆ hid.codes f := by
    intro j hj
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hj
    exact hid.hcodes f hf w
  calc ‖∑ j ∈ univ.image (hid.cls f), c (hid.rep f j) * ((hid.res f j : ℚ) : ℂ)‖
      ≤ ∑ j ∈ univ.image (hid.cls f), ‖c (hid.rep f j) * ((hid.res f j : ℚ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ univ.image (hid.cls f), M * |((hid.res f j : ℚ) : ℝ)| := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hn : ‖((hid.res f j : ℚ) : ℂ)‖ = |((hid.res f j : ℚ) : ℝ)| := by
          rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
        rw [norm_mul, hn]
        exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
    _ ≤ ∑ j ∈ hid.codes f, M * |((hid.res f j : ℚ) : ℝ)| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => mul_nonneg hM0 (abs_nonneg _)
    _ = M * ∑ j ∈ hid.codes f, |((hid.res f j : ℚ) : ℝ)| := by rw [Finset.mul_sum]

end IdFactS5

/-- Collapse of the family indicator over five families. -/
lemma fam_collapse5 (C : CertD) {ι : Type*} (S : Finset ι) (fam : ι → ℕ) (hfam : ∀ i ∈ S, fam i < 5)
    (c : ℕ → (Fin (C.k + 1) → Fin 24) → ℂ) (b : ι → (Fin (C.k + 1) → Fin 24) → ℂ) :
    ∑ f ∈ Finset.range 5, ∑ w, c f w * ∑ i ∈ S, (if fam i = f then b i w else 0) =
      ∑ i ∈ S, ∑ w, c (fam i) w * b i w := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, w]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun w _ => ?_
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [hfam i hi]

/-- **Expansion of the paired slack identity, five families.** -/
lemma LambdaS_expand5 (C : CertD) (α β : ℕ) (nu : ℚ) (c : ℕ → (Fin (C.k + 1) → Fin 24) → ℂ)
    (hfam : ∀ t ∈ C.types, ∀ r < t.nrows, ∀ s < t.nrows, (Sem.CertD.ruleOf t r s).fam < 5)
    (hpfam : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, P.fam < 5) :
    ∑ f ∈ Finset.range 5, ∑ w, c f w * ((ΛS C α β nu f w : ℚ) : ℂ) =
      ∑ w, c 0 w * ((objT C α β w : ℚ) : ℂ)
      - (nu : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 * ∑ w, c 0 w * ((trW C w : ℚ) : ℂ)
      - (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
          ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum
      - (C.eqs.map fun g => (g.parts.map fun P =>
          (P.sign : ℂ) * ∑ w, c P.fam w * ((C.eqVal g P w : ℚ) : ℂ)).sum).sum := by
  have hΛ : ∀ f w, ((ΛS C α β nu f w : ℚ) : ℂ) =
      (if f = 0 then ((objT C α β w : ℚ) : ℂ) - (nu : ℂ) * ((trW C w : ℚ) : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4
        else 0)
      - (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
          if ((t.rules.getD r []).getD s default).fam = f then ((C.blk t r s w : ℚ) : ℂ) else 0).sum
      - (C.eqs.map fun g => (g.parts.map fun P =>
          if P.fam = f then (P.sign : ℂ) * ((C.eqVal g P w : ℚ) : ℂ) else 0).sum).sum := by
    intro f w
    simp only [ΛS, Rat.cast_sub, Sem.CertD.cast_list_sum]
    congr 1
    · congr 1
      · split_ifs <;> push_cast <;> ring
      · refine Sem.CertD.list_sum_congr _ _ _ fun t _ => ?_
        push_cast
        refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
        split_ifs <;> simp
    · refine Sem.CertD.list_sum_congr _ _ _ fun g _ => ?_
      refine Sem.CertD.list_sum_congr _ _ _ fun P _ => ?_
      split_ifs <;> simp
  simp only [hΛ, mul_sub, Finset.sum_sub_distrib]
  have hobj : ∑ f ∈ Finset.range 5, ∑ w, c f w * (if f = 0 then ((objT C α β w : ℚ) : ℂ) -
        (nu : ℂ) * ((trW C w : ℚ) : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 else 0) =
      ∑ w, c 0 w * ((objT C α β w : ℚ) : ℂ)
        - (nu : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 * ∑ w, c 0 w * ((trW C w : ℚ) : ℂ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ↓reduceIte, mul_zero,
      Finset.sum_const_zero, add_zero, one_ne_zero, OfNat.ofNat_ne_zero]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hblk : ∑ f ∈ Finset.range 5, ∑ w, c f w *
      (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
          if ((t.rules.getD r []).getD s default).fam = f then ((C.blk t r s w : ℚ) : ℂ) else 0).sum =
      (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
          ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum := by
    simp only [Sem.CertD.mul_list_sum, Sem.CertD.sum_list_comm]
    refine Sem.CertD.list_sum_congr _ _ _ fun t ht => ?_
    have h := fam_collapse5 C (Finset.range t.nrows ×ˢ Finset.range t.nrows)
      (fun rs => ((t.rules.getD rs.1 []).getD rs.2 default).fam)
      (fun rs hrs => by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hrs
        exact hfam t ht _ hrs.1 _ hrs.2) c (fun rs w => ((C.blk t rs.1 rs.2 w : ℚ) : ℂ))
    simp only [Finset.sum_product] at h
    exact h
  have heq : ∑ f ∈ Finset.range 5, ∑ w, c f w *
      (C.eqs.map fun g => (g.parts.map fun P =>
          if P.fam = f then (P.sign : ℂ) * ((C.eqVal g P w : ℚ) : ℂ) else 0).sum).sum =
      (C.eqs.map fun g => (g.parts.map fun P =>
          (P.sign : ℂ) * ∑ w, c P.fam w * ((C.eqVal g P w : ℚ) : ℂ)).sum).sum := by
    simp only [Sem.CertD.mul_list_sum, Sem.CertD.sum_list_comm]
    refine Sem.CertD.list_sum_congr _ _ _ fun g hg => ?_
    refine Sem.CertD.list_sum_congr _ _ _ fun P hP => ?_
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_range, hpfam g hg P hP, ite_true]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [hobj, hblk, heq]

end NPT.K4

#print axioms NPT.K4.LambdaS_expand5
#print axioms NPT.K4.class_sum_res5
