/-
NPT.K4.SemS — the slack functional and the identity fact with claimed class residuals.

`ΛS α β nu f w = [f = 31]·(objT α β w − nu · trW w / (2 d^k)^4) − Σ blk − Σ sign·eq` is the functional
`Sem.CertD.Λ` with the objective at `t = β/α` and the trace multiplier `nu Tr X_31 / (2 d^k)^4` (in the verifier's
notation, `c_t / L` and `nu Tr X_31 / L`).  `IdFactS` is `IdFact` whose class sums of `ΛS` equal claimed residuals
`res f j` instead of 0, with a finite code set `codes f` containing every class code.  Paired with orbit-constant
coefficients, the identity becomes `Σ_f Σ_w c_f(w) ΛS_f(w) = Σ_f Σ_{j ∈ image} c_f(rep j) · res f j`
(`class_sum_res`), whose norm is at most `max ‖c‖ · Σ_{j ∈ codes f} |res f j|` per family (`res_bound`).
-/
import NPT.K4.ObjT
import NPT.Cert.Assembly

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem

namespace NPT.K4

/-- **The slack functional** (family codes 0/1/2 = '31'/'22'/'13'). -/
def ΛS (C : CertD) (α β : ℕ) (nu : ℚ) (f : ℕ) (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  (if f = 0 then objT C α β w - nu * trW C w / (2 * C.d ^ C.k) ^ 4 else 0)
  - (C.types.map fun t => ∑ r ∈ range t.nrows, ∑ s ∈ range t.nrows,
        if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0).sum
  - (C.eqs.map fun g => (g.parts.map fun P =>
        if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum).sum

lemma ΛS_eq (C : CertD) (α β : ℕ) (nu : ℚ) (f : ℕ) (w : Fin (C.k + 1) → Fin 24) :
    ΛS C α β nu f w = C.Λ f w +
      (if f = 0 then objT C α β w - C.obj w - nu * trW C w / (2 * C.d ^ C.k) ^ 4 else 0) := by
  unfold ΛS Sem.CertD.Λ
  split_ifs <;> ring

/-- **The identity fact with claimed residuals**: classes, representatives and witnesses as in `IdFact`; the class
sums of `ΛS` equal `res f (class)`; `codes f` is a finite set containing every class code of family `f`. -/
structure IdFactS (C : CertD) (α β : ℕ) (nu : ℚ) where
  cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ
  rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24)
  wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool
  hG : ∀ f < 3, ∀ w, inG f (wit f w).1 = true ∧ inG f (wit f w).2.1 = true
  hσ : ∀ f < 3, ∀ w, Function.Bijective (wit f w).2.2.1
  hrep : ∀ f < 3, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w)
  res : ℕ → ℕ → ℚ
  codes : ℕ → Finset ℕ
  hcodes : ∀ f < 3, ∀ w, cls f w ∈ codes f
  hsum : ∀ f < 3, ∀ w₀, ∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ΛS C α β nu f w = res f (cls f w₀)

section IdFactS

variable {C : CertD} {α β : ℕ} {nu : ℚ}

lemma class_constS (hid : IdFactS C α β nu) {f : ℕ} (hf : f < 3) (c : (Fin (C.k + 1) → Fin 24) → ℂ)
    (hinv : ∀ (g1 g2 : Fin 24) (σ : Fin C.k → Fin C.k) (ε : Bool) (w : Fin (C.k + 1) → Fin 24),
      inG f g1 = true → inG f g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w)
    (w : Fin (C.k + 1) → Fin 24) : c w = c (hid.rep f (hid.cls f w)) := by
  rw [← hid.hrep f hf w]
  exact (hinv _ _ _ _ w (hid.hG f hf w).1 (hid.hG f hf w).2 (hid.hσ f hf w)).symm

/-- **Class sums with residuals.** A coefficient function constant on the classes pairs with `ΛS_f` to the
residual sum over the classes that occur. -/
lemma class_sum_res (hid : IdFactS C α β nu) {f : ℕ} (hf : f < 3) (c : (Fin (C.k + 1) → Fin 24) → ℂ)
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

/-- **Residual bound**: with `‖c w‖ ≤ M` for every word, the residual sum of family `f` has norm at most
`M · Σ_{j ∈ codes f} |res f j|`. -/
lemma res_bound (hid : IdFactS C α β nu) {f : ℕ} (hf : f < 3) (c : (Fin (C.k + 1) → Fin 24) → ℂ) {M : ℝ}
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

end IdFactS

/-- **Expansion** of the paired slack identity: objective at `t`, the trace term, blocks and equalities. -/
lemma LambdaS_expand (C : CertD) (α β : ℕ) (nu : ℚ) (c : ℕ → (Fin (C.k + 1) → Fin 24) → ℂ)
    (hfam : ∀ t ∈ C.types, ∀ r < t.nrows, ∀ s < t.nrows, (Sem.CertD.ruleOf t r s).fam < 3)
    (hpfam : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, P.fam < 3) :
    ∑ f ∈ Finset.range 3, ∑ w, c f w * ((ΛS C α β nu f w : ℚ) : ℂ) =
      ∑ w, c 0 w * ((objT C α β w : ℚ) : ℂ)
      - (nu : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 * ∑ w, c 0 w * ((trW C w : ℚ) : ℂ)
      - (C.types.map fun t => ∑ r ∈ Finset.range t.nrows, ∑ s ∈ Finset.range t.nrows,
          ∑ w, c (Sem.CertD.ruleOf t r s).fam w * ((C.blk t r s w : ℚ) : ℂ)).sum
      - (C.eqs.map fun g => (g.parts.map fun P =>
          (P.sign : ℂ) * ∑ w, c P.fam w * ((C.eqVal g P w : ℚ) : ℂ)).sum).sum := by
  have h1 : ∀ f w, ((ΛS C α β nu f w : ℚ) : ℂ) = ((C.Λ f w : ℚ) : ℂ) +
      (if f = 0 then ((objT C α β w : ℚ) : ℂ) - ((C.obj w : ℚ) : ℂ) -
        (nu : ℂ) * ((trW C w : ℚ) : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 else 0) := by
    intro f w
    rw [ΛS_eq]
    split_ifs <;> push_cast <;> ring
  simp only [h1, mul_add, Finset.sum_add_distrib]
  rw [C.Lambda_expand c hfam hpfam]
  have h2 : ∑ f ∈ Finset.range 3, ∑ w, c f w * (if f = 0 then ((objT C α β w : ℚ) : ℂ) - ((C.obj w : ℚ) : ℂ) -
        (nu : ℂ) * ((trW C w : ℚ) : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 else 0) =
      ∑ w, c 0 w * ((objT C α β w : ℚ) : ℂ) - ∑ w, c 0 w * ((C.obj w : ℚ) : ℂ)
        - (nu : ℂ) / (2 * (C.d : ℂ) ^ C.k) ^ 4 * ∑ w, c 0 w * ((trW C w : ℚ) : ℂ) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ↓reduceIte, mul_zero,
      Finset.sum_const_zero, add_zero, one_ne_zero, OfNat.ofNat_ne_zero]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [h2]
  ring

end NPT.K4

#print axioms NPT.K4.class_sum_res
#print axioms NPT.K4.LambdaS_expand
