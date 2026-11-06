/-
NPT.K4.ObjT — the objective at a general endpoint `t = β/α`, and the trace term.

`OobjT α β = ⊗_sites (α I − β F03) ⊗ F03_aux = Σ_J (−β)^|J| α^(k−|J|) F^{J ∪ aux}`.  For the family-31 moment
operator of `C = A Bᴴ`: `Tr(OobjT α β · X_31) = ‖a‖⁴ · α^k · q(β/α, A Bᴴ)` when `α ≠ 0` (`obj_physT`).  This is the
proof of `NPT.Cert.Phys.obj_phys` with `2 ↦ α`, `1 ↦ β`, reusing its helper lemmas.  `OobjT` is invariant under
site permutations, has real entries, is Hermitian and lies in the word span, so `Tr(OobjT · ·)` does not change
under the projection onto the span (`trace_OobjT_proj`).

Semantic side: `objT` is the per-word objective `Π_sites (α tr V − β tr F03 V) · tr F03 V_aux / (α^k (2 d^k)^4)`,
linked to the operator by `objT_eq` / `sum_objT` (as `Sem.CertD.obj_eq` / `sum_obj`); `trW w = Π_l tr V_{w_l}` is
the trace of the word operator (`trW_eq`, `sum_trW`), and the projection keeps the trace (`trace_proj`).
-/
import NPT.Cert.PhysObj
import NPT.Cert.PhysSym
import NPT.Cert.SoundPrep

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Phys NPT.Cert.Phys.Obj

namespace NPT.K4

variable {k d : ℕ}

/-! ### The objective operator at a general endpoint -/

variable (k d) in
/-- Objective operator at `t = β/α`: `⊗_sites (α I − β F03) ⊗ F03_aux` (`F03` = PERMS index 21). -/
noncomputable def OobjT (α β : ℝ) : Matrix (GI (nf k d)) (GI (nf k d)) ℂ :=
  kron fun l => if l.val < k then (α : ℂ) • VG ℂ (nf k d l) 0 0 - (β : ℂ) • VG ℂ (nf k d l) 0 21
    else VG ℂ (nf k d l) 0 21

lemma OobjT_apply (α β : ℝ) (i j : GI (nf k d)) :
    OobjT k d α β i j = ∏ l, (if l.val < k then
      (α : ℂ) * (if j l = i l then (1 : ℂ) else 0) - (β : ℂ) * (if j l = i l ∘ pinvf 21 then 1 else 0)
      else (if j l = i l ∘ pinvf 21 then 1 else 0)) := by
  unfold OobjT kron
  refine Finset.prod_congr rfl fun l _ => ?_
  by_cases hl : l.val < k
  · simp only [hl, ite_true, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      VG_zero (by norm_num : (0 : ℕ) < 16), Matrix.one_apply, F03_apply, eq_comm]
  · simp only [hl, ite_false, F03_apply]

/-- `OobjT = Σ_J (-β)^|J| α^(k-|J|) F^{J ∪ aux}`, entrywise. -/
lemma OobjT_apply_expand (α β : ℝ) (i j : GI (nf k d)) :
    OobjT k d α β i j = ∑ J : Finset (Fin k), ((-(β : ℂ)) ^ J.card * (α : ℂ) ^ (k - J.card)) *
      (if j = tau (swapSet J) i then 1 else 0) := by
  rw [OobjT_apply, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_irrefl, ite_false]
  set φ : Fin (k + 1) → ℂ := fun l => if j l = i l ∘ pinvf 21 then 1 else 0 with hφ
  set δ : Fin (k + 1) → ℂ := fun l => if j l = i l then 1 else 0 with hδ
  have hexp : ∏ s : Fin k, ((α : ℂ) * δ s.castSucc - (β : ℂ) * φ s.castSucc) =
      ∑ J : Finset (Fin k), (∏ s ∈ J, -((β : ℂ) * φ s.castSucc)) * ∏ s ∈ univ \ J, (α : ℂ) * δ s.castSucc := by
    rw [← Finset.powerset_univ, ← Finset.prod_add]
    exact Finset.prod_congr rfl fun s _ => by ring
  rw [hexp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hind : (if j = tau (swapSet J) i then (1 : ℂ) else 0) =
      (∏ s, (if s ∈ J then φ s.castSucc else δ s.castSucc)) * φ (Fin.last k) := by
    have h1 : (if j = tau (swapSet J) i then (1 : ℂ) else 0) =
        ∏ l, (if j l = tau (swapSet J) i l then (1 : ℂ) else 0) := by
      rw [Fintype.prod_boole]
      by_cases h : j = tau (swapSet J) i
      · rw [ite_eq_left h, ite_eq_left (fun l => congrFun h l)]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h (funext h'))]
    rw [h1, Fin.prod_univ_castSucc]
    congr 1
    · refine Finset.prod_congr rfl fun s _ => ?_
      by_cases hs : s ∈ J
      · simp only [hs, ite_true, hφ, tau, (castSucc_mem_swapSet J s).2 hs]
      · simp only [hs, ite_false, hδ, tau, mt (castSucc_mem_swapSet J s).1 hs]
    · simp only [hφ, tau, last_mem_swapSet, ite_true]
  rw [hind, prod_ite_mem_univ]
  simp only [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ, Fintype.card_fin]
  simp only [hφ]
  ring

lemma traceT_expand (α β : ℝ) (a b : V1 k d → ℂ) :
    (OobjT k d α β * Xf 0 a b).trace = ∑ J : Finset (Fin k), ((-(β : ℂ)) ^ J.card * (α : ℂ) ^ (k - J.card)) *
      ∑ i, star (patVec (famPat 0) a b i) * patVec (famPat 0) a b (tau (swapSet J) i) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Xf, vecMulVec_apply, Pi.star_apply,
    OobjT_apply_expand, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  ring

/-- **Objective identity at `t = β/α`.** -/
theorem obj_physT [NeZero d] (α β : ℝ) (hα : α ≠ 0) (A B : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    (OobjT k d α β * Xf 0 (vecOf A) (vecOf B)).trace =
      (((nsq k d (vecOf A)) ^ 2 * α ^ k * NPT.q (β / α) (A * Bᴴ) : ℝ) : ℂ) := by
  rw [traceT_expand]
  simp only [term_J]
  unfold NPT.q
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  have hc : J.card ≤ k := by simpa using Finset.card_le_univ J
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  have h2 : (α : ℂ) ^ k = (α : ℂ) ^ (k - J.card) * (α : ℂ) ^ J.card := by
    rw [← pow_add, Nat.sub_add_cancel hc]
  have h3 : (-((β : ℂ) / (α : ℂ))) ^ J.card * (α : ℂ) ^ J.card = (-(β : ℂ)) ^ J.card := by
    rw [← mul_pow, neg_mul, div_mul_cancel₀ _ hα']
  rw [h2]
  linear_combination (-(α : ℂ) ^ (k - J.card) * (nsq k d (vecOf A) : ℂ) ^ 2 *
    (NPT.frobSq (NPT.ptrace J (A * Bᴴ)) : ℂ)) * h3

/-! ### Invariances of `OobjT` -/

lemma OlocT_cast (α β : ℝ) (l l' : Fin (k + 1)) (h : nf k d l' = nf k d l) (hl : l'.val < k ↔ l.val < k)
    (x y : Dig (nf k d l') 4) :
    (if l.val < k then (α : ℂ) • VG ℂ (nf k d l) 0 0 - (β : ℂ) • VG ℂ (nf k d l) 0 21 else VG ℂ (nf k d l) 0 21)
        (fun r => Fin.cast h (x r)) (fun r => Fin.cast h (y r)) =
      (if l'.val < k then (α : ℂ) • VG ℂ (nf k d l') 0 0 - (β : ℂ) • VG ℂ (nf k d l') 0 21
        else VG ℂ (nf k d l') 0 21) x y := by
  by_cases hl' : l'.val < k
  · rw [ite_eq_left (hl.mp hl'), ite_eq_left hl']
    simp only [Matrix.sub_apply, Matrix.smul_apply, SymAux.VG_cast]
  · rw [ite_eq_right (fun h' => hl' (hl.mpr h')), ite_eq_right hl']
    exact SymAux.VG_cast h 0 21 x y

theorem siteAct_OobjT (σ : Equiv.Perm (Fin k)) (α β : ℝ) : siteAct σ (OobjT k d α β) = OobjT k d α β := by
  ext i j
  simp only [siteAct, OobjT, kron]
  exact Fintype.prod_equiv (sigHat σ) _ _ fun l =>
    OlocT_cast α β l (sigHat σ l) (nf_sigHat σ l) (sigHat_lt σ l) (i (sigHat σ l)) (j (sigHat σ l))

theorem trace_OobjT_siteAct (σ : Equiv.Perm (Fin k)) (α β : ℝ) (M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) :
    (OobjT k d α β * siteAct σ M).trace = (OobjT k d α β * M).trace := by
  rw [← SymAux.trace_siteAct_mul σ (OobjT k d α β) M, siteAct_OobjT]

lemma star_OobjT (α β : ℝ) (i j : GI (nf k d)) : star (OobjT k d α β i j) = OobjT k d α β i j := by
  simp only [OobjT, kron, star_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, star_sub, star_mul', SymAux.star_VG0,
      Complex.star_def, Complex.conj_ofReal]
  · exact SymAux.star_VG0 _ _ _

theorem trace_OobjT_conjM (α β : ℝ) (M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) :
    (OobjT k d α β * conjM M).trace = star ((OobjT k d α β * M).trace) := by
  simp only [Matrix.trace, Matrix.diag, mul_apply, conjM, Matrix.map_apply, star_sum, star_mul',
    star_OobjT]

lemma OlocT_mem (α β : ℝ) (l : Fin (k + 1)) :
    (if l.val < k then (α : ℂ) • VG ℂ (nf k d l) 0 0 - (β : ℂ) • VG ℂ (nf k d l) 0 21
      else VG ℂ (nf k d l) 0 21) ∈ Submodule.span ℂ (Set.range (VG ℂ (nf k d l) 0)) := by
  split_ifs
  · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨21, rfl⟩))
  · exact Submodule.subset_span ⟨21, rfl⟩

lemma OobjT_mem (α β : ℝ) : OobjT k d α β ∈ spanS (nf := nf k d) 0 :=
  kron_mem_span (fun l => VG ℂ (nf k d l) 0) (fun l => OlocT_mem α β l)

lemma OobjT_conjTranspose (α β : ℝ) : (OobjT k d α β)ᴴ = OobjT k d α β := by
  unfold OobjT
  rw [kron_conjTranspose]
  congr 1
  funext l
  split_ifs
  · rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, VG_zero (by norm_num), conjTranspose_one,
      VG21_conjTranspose]
    simp [Complex.conj_ofReal]
  · exact VG21_conjTranspose

lemma trace_OobjT_proj (α β : ℝ) {X Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}
    (h : IsProj (spanS (nf := nf k d) 0) X Y) :
    (OobjT k d α β * Y).trace = (OobjT k d α β * X).trace := by
  have := h.2 _ (OobjT_mem α β)
  rwa [OobjT_conjTranspose] at this

/-- The projection onto the word span keeps the trace (the identity word lies in the span). -/
lemma trace_proj {X Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ} (h : IsProj (spanS (nf := nf k d) 0) X Y) :
    Y.trace = X.trace := by
  have := h.2 _ (VW_mem (nf := nf k d) 0 (fun _ => 0))
  rwa [VW_zero (by norm_num), conjTranspose_one, Matrix.one_mul, Matrix.one_mul] at this

/-! ### Semantic objective and trace term -/

/-- Objective at `t = β/α` (ep3core `objective_tensor` with `2 ↦ α`, `1 ↦ β`): sites `α tr V_p − β tr F03 V_p`
at `n = d`, aux `tr F03 V_p` at `n = 2`, divided by `α^k (2 d^k)^4`. -/
def objT (C : CertD) (α β : ℕ) (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  (∏ l : Fin C.k, ((α : ℚ) * trace (VG ℚ C.d 0 (w l.castSucc)) -
      (β : ℚ) * trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 (w l.castSucc)))) *
    trace (VG ℚ 2 0 21 * VG ℚ 2 0 (w (Fin.last C.k))) / ((α : ℚ) ^ C.k * (2 * C.d ^ C.k) ^ 4)

/-- Trace of the word operator: `tr V_w = Π_l tr V_{w_l}` (dimension `n_l` at factor `l`). -/
def trW (C : CertD) (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  ∏ l : Fin (C.k + 1), trace (VG ℚ (nf C.k C.d l) 0 (w l))

lemma OobjT_mul_VW (C : CertD) (α β : ℝ) (w : Fin (C.k + 1) → Fin 24) :
    OobjT C.k C.d α β * VW (nf C.k C.d) 0 w =
      kron fun l => (if l.val < C.k then (α : ℂ) • VG ℂ (nf C.k C.d l) 0 0 - (β : ℂ) • VG ℂ (nf C.k C.d l) 0 21
        else VG ℂ (nf C.k C.d l) 0 21) * VG ℂ (nf C.k C.d l) 0 (w l) := by
  unfold OobjT VW
  rw [kron_mul]

/-- **Per-word objective link** at `t = β/α`. -/
lemma objT_eq (C : CertD) (α β : ℕ) (w : Fin (C.k + 1) → Fin 24) :
    ((objT C α β w : ℚ) : ℂ) = (OobjT C.k C.d α β * VW (nf C.k C.d) 0 w).trace /
      ((α : ℂ) ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4) := by
  rw [OobjT_mul_VW, trace_kron, Fin.prod_univ_castSucc]
  unfold objT
  push_cast
  congr 1
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (i.castSucc : Fin (C.k + 1)).val < C.k := by simp
    rw [ite_eq_left hi, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, VG_zero (by norm_num),
      Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    simp only [cq_trace, cq_mul, cq_VG]
    have h := Phys.nf_site C.k C.d i
    exact (Sem.CertD.trace_fun_congr h (fun m => (α : ℂ) * (VG ℂ m 0 (w i.castSucc)).trace -
      (β : ℂ) * (VG ℂ m 0 21 * VG ℂ m 0 (w i.castSucc)).trace)).symm
  · rw [ite_eq_right (lt_irrefl C.k)]
    simp only [cq_trace, cq_mul, cq_VG]
    exact (Sem.CertD.trace_fun_congr (Phys.nf_aux C.k C.d) (fun m =>
      (VG ℂ m 0 21 * VG ℂ m 0 (w (Fin.last C.k))).trace)).symm

lemma sum_objT (C : CertD) (α β : ℕ) (c : (Fin (C.k + 1) → Fin 24) → ℂ) :
    ∑ w, c w * ((objT C α β w : ℚ) : ℂ) = (OobjT C.k C.d α β * ∑ w, c w • VW (nf C.k C.d) 0 w).trace /
      ((α : ℂ) ^ C.k * (2 * (C.d : ℂ) ^ C.k) ^ 4) := by
  simp only [objT_eq, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Finset.sum_div, mul_div_assoc]

lemma trW_eq (C : CertD) (w : Fin (C.k + 1) → Fin 24) :
    ((trW C w : ℚ) : ℂ) = (VW (nf C.k C.d) 0 w).trace := by
  unfold trW VW
  rw [trace_kron]
  push_cast
  simp only [cq_trace, cq_VG]

lemma sum_trW (C : CertD) (c : (Fin (C.k + 1) → Fin 24) → ℂ) :
    ∑ w, c w * ((trW C w : ℚ) : ℂ) = (∑ w, c w • VW (nf C.k C.d) 0 w).trace := by
  simp only [trW_eq, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]

end NPT.K4

#print axioms NPT.K4.obj_physT
#print axioms NPT.K4.objT_eq
