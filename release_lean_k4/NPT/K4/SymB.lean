/-
NPT.K4.SymB — orbit-constant coefficients that keep a bound.

`NPT.Cert.sym_coeffs` symmetrizes some coefficients of the projection `Y` in three averaging stages (`G_f × G_f`, the
site permutations, inversion).  Here the same stages start from given coefficients `c₀` with `‖c₀ w‖ ≤ M` and keep the
bound: every stage replaces `c` by an average of transported copies of `c`.  (Proofs of the stages follow
`NPT.Cert.SymAvg.stage1–3` verbatim, plus the bound.)
-/
import NPT.Cert.Sym

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg

namespace NPT.K4

variable {k d : ℕ} {f : ℕ} {Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}

lemma avg_norm_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (F : ι → ℂ) {M : ℝ} (hF : ∀ i ∈ s, ‖F i‖ ≤ M) :
    ‖(s.card : ℂ)⁻¹ * ∑ i ∈ s, F i‖ ≤ M := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (s.card : ℝ)⁻¹ * ‖∑ i ∈ s, F i‖ ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖F i‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.2 hc.le)
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _i ∈ s, M := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (inv_nonneg.2 hc.le)
    _ = M := by rw [Finset.sum_const, nsmul_eq_mul]; field_simp

lemma stage1B (YG : ∀ g h : Fin 24, inG f g = true → inG f h = true → VWc g * Y * VWc h = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w) {M : ℝ} (hM : ∀ w, ‖c w‖ ≤ M) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧ ∀ w, ‖c' w‖ ≤ M := by
  have hne : (Gf f ×ˢ Gf f).Nonempty :=
    ⟨(0, 0), Finset.mem_product.2 ⟨mem_Gf.2 (inG_one f), mem_Gf.2 (inG_one f)⟩⟩
  refine ⟨fun w => ((Gf f ×ˢ Gf f).card : ℂ)⁻¹ * ∑ p ∈ Gf f ×ˢ Gf f, c ((tauGH k p.1 p.2).symm w),
    ?_, ?_, fun w => avg_norm_le _ hne _ fun p _ => hM _⟩
  · refine rep_avg _ hne (fun p w => c ((tauGH k p.1 p.2).symm w)) fun p hp => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact rep_transport (Tgh k d p.1 p.2) (tauGH k p.1 p.2) (Tgh_VW p.1 p.2)
      (YG p.1 p.2 (mem_Gf.1 h1) (mem_Gf.1 h2)) hc
  · intro g h hg hh w
    dsimp only
    congr 1
    refine Finset.sum_nbij' (fun p => (mulIdx (pinvIdx g) p.1, mulIdx p.2 (pinvIdx h)))
      (fun q => (mulIdx g q.1, mulIdx q.2 h)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      exact Finset.mem_product.2 ⟨mem_Gf.2 (inG_mul (inG_pinv hg) (mem_Gf.1 h1)),
        mem_Gf.2 (inG_mul (mem_Gf.1 h2) (inG_pinv hh))⟩
    · intro q hq
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
      exact Finset.mem_product.2 ⟨mem_Gf.2 (inG_mul hg (mem_Gf.1 h1)),
        mem_Gf.2 (inG_mul (mem_Gf.1 h2) hh)⟩
    · intro p _
      refine Prod.ext ?_ ?_ <;>
        (apply permE_injective; simp only [permE_mul, permE_pinv]; group)
    · intro q _
      refine Prod.ext ?_ ?_ <;>
        (apply permE_injective; simp only [permE_mul, permE_pinv]; group)
    · intro p _
      congr 1
      funext l
      simp only [tauGH, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
      apply permE_injective
      simp only [permE_mul, permE_pinv]
      group

lemma stage2B (YS : ∀ σ : Equiv.Perm (Fin k), siteAct σ Y = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w)
    (hcG : ∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c (tauGH k g h w) = c w)
    {M : ℝ} (hM : ∀ w, ‖c w‖ ≤ M) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧
      (∀ (σ : Equiv.Perm (Fin k)) w, c' (tauS k σ w) = c' w) ∧ ∀ w, ‖c' w‖ ≤ M := by
  refine ⟨fun w => ((univ : Finset (Equiv.Perm (Fin k))).card : ℂ)⁻¹ * ∑ σ, c ((tauS k σ).symm w),
    ?_, ?_, ?_, fun w => avg_norm_le _ univ_nonempty _ fun σ _ => hM _⟩
  · exact rep_avg univ univ_nonempty (fun σ w => c ((tauS k σ).symm w)) fun σ _ =>
      rep_transport (Tsite k d σ) (tauS k σ) (Tsite_VW σ) (YS σ) hc
  · intro g h hg hh w
    dsimp only
    congr 1
    exact Finset.sum_congr rfl fun σ _ => hcG g h hg hh ((tauS k σ).symm w)
  · intro τ w
    dsimp only
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft τ⁻¹) _ _ fun σ => ?_
    congr 1
    funext l
    simp only [tauS, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Function.comp_apply, Equiv.coe_mulLeft,
      sigHat_mul, Equiv.Perm.inv_def]

lemma stage3B (YT : Yᵀ = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w)
    (hcG : ∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c (tauGH k g h w) = c w)
    (hcS : ∀ (σ : Equiv.Perm (Fin k)) w, c (tauS k σ w) = c w) {M : ℝ} (hM : ∀ w, ‖c w‖ ≤ M) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, inG f g = true → inG f h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧
      (∀ (σ : Equiv.Perm (Fin k)) w, c' (tauS k σ w) = c' w) ∧ (∀ w, c' (tauT k w) = c' w) ∧
      ∀ w, ‖c' w‖ ≤ M := by
  refine ⟨fun w => ((univ : Finset Bool).card : ℂ)⁻¹ * ∑ b, cond b (c ((tauT k).symm w)) (c w),
    ?_, ?_, ?_, ?_, fun w => avg_norm_le _ univ_nonempty _ fun b _ => by cases b <;> exact hM _⟩
  · refine rep_avg univ univ_nonempty (fun b w => cond b (c ((tauT k).symm w)) (c w)) fun b _ => ?_
    cases b
    · exact hc
    · exact rep_transport (Ttr k d) (tauT k) Ttr_VW YT hc
  · intro g h hg hh w
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    cases b
    · exact hcG g h hg hh w
    · have e : (tauT k).symm (tauGH k g h w) = tauGH k (pinvIdx h) (pinvIdx g) ((tauT k).symm w) := by
        funext l
        simp only [tauT, tauGH, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
        apply permE_injective
        simp only [permE_mul, permE_pinv]
        group
      show c ((tauT k).symm (tauGH k g h w)) = c ((tauT k).symm w)
      rw [e]
      exact hcG _ _ (inG_pinv hh) (inG_pinv hg) _
  · intro σ w
    dsimp only
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    cases b
    · exact hcS σ w
    · exact hcS σ ((tauT k).symm w)
  · intro w
    dsimp only
    congr 1
    simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, Equiv.symm_apply_apply]
    rw [add_comm]
    rfl

/-- **Orbit-constant coefficients with a bound**: as `NPT.Cert.sym_coeffs`, starting from coefficients `c₀` of `Y`
with `‖c₀ w‖ ≤ M`; the result keeps the bound. -/
theorem sym_coeffs_bdd {X : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}
    (hY : IsProj (spanS (nf := nf k d) 0) X Y)
    (hG : ∀ g h : Fin 24, inG f g = true → inG f h = true → VWc g * X * VWc h = X)
    (hS : ∀ σ : Equiv.Perm (Fin k), siteAct σ X = X)
    (hT : Xᵀ = X) {c₀ : (Fin (k + 1) → Fin 24) → ℂ} (hc₀ : Y = ∑ w, c₀ w • VW (nf k d) 0 w)
    {M : ℝ} (hM : ∀ w, ‖c₀ w‖ ≤ M) :
    ∃ c : (Fin (k + 1) → Fin 24) → ℂ, Y = ∑ w, c w • VW (nf k d) 0 w ∧
      (∀ (g1 g2 : Fin 24) (σ : Fin k → Fin k) (ε : Bool) (w : Fin (k + 1) → Fin 24),
        inG f g1 = true → inG f g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w) ∧
      ∀ w, ‖c w‖ ≤ M := by
  have YG : ∀ g h : Fin 24, inG f g = true → inG f h = true → VWc g * Y * VWc h = Y :=
    fun g h hg hh => proj_inv (Tgh k d g h) (fun w => by rw [Tgh_VW]; exact VW_mem 0 _) (Tgh_adj g h)
      hY (hG g h hg hh)
  have YS : ∀ σ : Equiv.Perm (Fin k), siteAct σ Y = Y :=
    fun σ => proj_inv (Tsite k d σ) (fun w => by rw [Tsite_VW]; exact VW_mem 0 _) (Tsite_adj σ) hY (hS σ)
  have YT : Yᵀ = Y := proj_inv (Ttr k d) (fun w => by rw [Ttr_VW]; exact VW_mem 0 _) Ttr_adj hY hT
  obtain ⟨c₁, hc₁, hG₁, hM₁⟩ := stage1B YG hc₀ hM
  obtain ⟨c₂, hc₂, hG₂, hS₂, hM₂⟩ := stage2B YS hc₁ hG₁ hM₁
  obtain ⟨c₃, hc₃, hG₃, hS₃, hT₃, hM₃⟩ := stage3B YT hc₂ hG₂ hS₂ hM₂
  refine ⟨c₃, hc₃, fun g1 g2 σ ε w hg1 hg2 hσ => ?_, hM₃⟩
  rw [act_eq g1 g2 hσ ε w]
  cases ε
  · exact (hG₃ g1 g2 hg1 hg2 _).trans (hS₃ _ w)
  · exact (hT₃ _).trans ((hG₃ g1 g2 hg1 hg2 _).trans (hS₃ _ w))

end NPT.K4
