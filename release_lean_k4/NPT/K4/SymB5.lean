/-
NPT.K4.SymB5 — bounded orbit-constant coefficients for an arbitrary family group (five-family certificate).

`NPT.K4.sym_coeffs_bdd` averages over `G_f × G_f` with `G_f` given by `Sem.inG f` (families 31/22/13).  The five-family
families 40 and 04 have the whole `S_4` as family group, so their classes are `S_4`-orbits.  Here the group is any
predicate `G : Fin 24 → Bool` closed under products and inverses and containing the identity (`GrpOK G`); the three
averaging stages are those of `SymB` (`NPT.Cert.SymAvg.stage1–3` plus the bound) with `inG f` replaced by `G`.
`inG5_grp` gives the instances for the five families (`decide +kernel`).
-/
import NPT.K4.SymB
import NPT.K4.Phys5

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg

namespace NPT.K4

/-- A subgroup of `S_4`, as a Boolean predicate on permutation indices. -/
structure GrpOK (G : Fin 24 → Bool) : Prop where
  one : G 0 = true
  mul : ∀ g h : Fin 24, G g = true → G h = true → G (mulIdx g h) = true
  inv : ∀ g : Fin 24, G g = true → G (pinvIdx g) = true

lemma inG5_one : ∀ f : Fin 5, inG5 f.val 0 = true := by decide +kernel
lemma inG5_mul : ∀ f : Fin 5, ∀ g h : Fin 24, inG5 f.val g = true → inG5 f.val h = true →
    inG5 f.val (mulIdx g h) = true := by decide +kernel
lemma inG5_inv : ∀ f : Fin 5, ∀ g : Fin 24, inG5 f.val g = true → inG5 f.val (pinvIdx g) = true := by
  decide +kernel

lemma inG5_grp {f : ℕ} (hf : f < 5) : GrpOK (inG5 f) :=
  ⟨inG5_one ⟨f, hf⟩, inG5_mul ⟨f, hf⟩, inG5_inv ⟨f, hf⟩⟩

variable {k d : ℕ} {G : Fin 24 → Bool} {Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}

lemma stage1G (hG : GrpOK G) (YG : ∀ g h : Fin 24, G g = true → G h = true → VWc g * Y * VWc h = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w) {M : ℝ} (hM : ∀ w, ‖c w‖ ≤ M) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, G g = true → G h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧ ∀ w, ‖c' w‖ ≤ M := by
  set GS : Finset (Fin 24) := univ.filter fun g => G g = true with hGS
  have memGS : ∀ {g : Fin 24}, g ∈ GS ↔ G g = true := by intro g; simp [hGS]
  have hne : (GS ×ˢ GS).Nonempty := ⟨(0, 0), Finset.mem_product.2 ⟨memGS.2 hG.one, memGS.2 hG.one⟩⟩
  refine ⟨fun w => ((GS ×ˢ GS).card : ℂ)⁻¹ * ∑ p ∈ GS ×ˢ GS, c ((tauGH k p.1 p.2).symm w),
    ?_, ?_, fun w => avg_norm_le _ hne _ fun p _ => hM _⟩
  · refine rep_avg _ hne (fun p w => c ((tauGH k p.1 p.2).symm w)) fun p hp => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
    exact rep_transport (Tgh k d p.1 p.2) (tauGH k p.1 p.2) (Tgh_VW p.1 p.2)
      (YG p.1 p.2 (memGS.1 h1) (memGS.1 h2)) hc
  · intro g h hg hh w
    dsimp only
    congr 1
    refine Finset.sum_nbij' (fun p => (mulIdx (pinvIdx g) p.1, mulIdx p.2 (pinvIdx h)))
      (fun q => (mulIdx g q.1, mulIdx q.2 h)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hp
      exact Finset.mem_product.2 ⟨memGS.2 (hG.mul _ _ (hG.inv _ hg) (memGS.1 h1)),
        memGS.2 (hG.mul _ _ (memGS.1 h2) (hG.inv _ hh))⟩
    · intro q hq
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
      exact Finset.mem_product.2 ⟨memGS.2 (hG.mul _ _ hg (memGS.1 h1)),
        memGS.2 (hG.mul _ _ (memGS.1 h2) hh)⟩
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

lemma stage2G (YS : ∀ σ : Equiv.Perm (Fin k), siteAct σ Y = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w)
    (hcG : ∀ g h : Fin 24, G g = true → G h = true → ∀ w, c (tauGH k g h w) = c w)
    {M : ℝ} (hM : ∀ w, ‖c w‖ ≤ M) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, G g = true → G h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧
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

lemma stage3G (hG : GrpOK G) (YT : Yᵀ = Y)
    {c : (Fin (k + 1) → Fin 24) → ℂ} (hc : Y = ∑ w, c w • VW (nf k d) 0 w)
    (hcG : ∀ g h : Fin 24, G g = true → G h = true → ∀ w, c (tauGH k g h w) = c w)
    (hcS : ∀ (σ : Equiv.Perm (Fin k)) w, c (tauS k σ w) = c w) {M : ℝ} (hM : ∀ w, ‖c w‖ ≤ M) :
    ∃ c' : (Fin (k + 1) → Fin 24) → ℂ, (Y = ∑ w, c' w • VW (nf k d) 0 w) ∧
      (∀ g h : Fin 24, G g = true → G h = true → ∀ w, c' (tauGH k g h w) = c' w) ∧
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
      exact hcG _ _ (hG.inv _ hh) (hG.inv _ hg) _
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

/-- **Orbit-constant coefficients with a bound, any family group** (as `sym_coeffs_bdd`). -/
theorem sym_coeffs_bddG (hG : GrpOK G) {X : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}
    (hY : IsProj (spanS (nf := nf k d) 0) X Y)
    (hXG : ∀ g h : Fin 24, G g = true → G h = true → VWc g * X * VWc h = X)
    (hS : ∀ σ : Equiv.Perm (Fin k), siteAct σ X = X)
    (hT : Xᵀ = X) {c₀ : (Fin (k + 1) → Fin 24) → ℂ} (hc₀ : Y = ∑ w, c₀ w • VW (nf k d) 0 w)
    {M : ℝ} (hM : ∀ w, ‖c₀ w‖ ≤ M) :
    ∃ c : (Fin (k + 1) → Fin 24) → ℂ, Y = ∑ w, c w • VW (nf k d) 0 w ∧
      (∀ (g1 g2 : Fin 24) (σ : Fin k → Fin k) (ε : Bool) (w : Fin (k + 1) → Fin 24),
        G g1 = true → G g2 = true → Function.Bijective σ → c (act g1 g2 σ ε w) = c w) ∧
      ∀ w, ‖c w‖ ≤ M := by
  have YG : ∀ g h : Fin 24, G g = true → G h = true → VWc g * Y * VWc h = Y :=
    fun g h hg hh => proj_inv (Tgh k d g h) (fun w => by rw [Tgh_VW]; exact VW_mem 0 _) (Tgh_adj g h)
      hY (hXG g h hg hh)
  have YS : ∀ σ : Equiv.Perm (Fin k), siteAct σ Y = Y :=
    fun σ => proj_inv (Tsite k d σ) (fun w => by rw [Tsite_VW]; exact VW_mem 0 _) (Tsite_adj σ) hY (hS σ)
  have YT : Yᵀ = Y := proj_inv (Ttr k d) (fun w => by rw [Ttr_VW]; exact VW_mem 0 _) Ttr_adj hY hT
  obtain ⟨c₁, hc₁, hG₁, hM₁⟩ := stage1G hG YG hc₀ hM
  obtain ⟨c₂, hc₂, hG₂, hS₂, hM₂⟩ := stage2G YS hc₁ hG₁ hM₁
  obtain ⟨c₃, hc₃, hG₃, hS₃, hT₃, hM₃⟩ := stage3G hG YT hc₂ hG₂ hS₂ hM₂
  refine ⟨c₃, hc₃, fun g1 g2 σ ε w hg1 hg2 hσ => ?_, hM₃⟩
  rw [act_eq g1 g2 hσ ε w]
  cases ε
  · exact (hG₃ g1 g2 hg1 hg2 _).trans (hS₃ _ w)
  · exact (hT₃ _).trans ((hG₃ g1 g2 hg1 hg2 _).trans (hS₃ _ w))

end NPT.K4

#print axioms NPT.K4.sym_coeffs_bddG
#print axioms NPT.K4.inG5_mul
