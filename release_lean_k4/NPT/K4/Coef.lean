/-
NPT.K4.Coef — bounded coefficients of the projection onto the word span.

For a PSD operator `X` on the global index space and its HS projection `Y` onto `span {VW w}`, there are
coefficients `c` with `Y = Σ_w c w • VW w` and `‖c w‖ ≤ Kc k · re (tr X)` for every word, where
`Kc k = (786/8640)^k · (496/2880)` (`= (131/1440)^k · (31/180)`, the row-sum norms of the leg inverses `NPT.K4.Gram`).
Route: `c = H g` with `g v = tr (VW vᴴ X)` and `H` the Kronecker product of the leg generalized inverses
(`G H G = G` per leg, kernel-checked); `|g v| ≤ re (tr X)` because `VW v` is a permutation matrix.
-/
import NPT.K4.Gram
import NPT.Cert.Sym
import NPT.Cert.SemLink

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Ident
open scoped ComplexOrder

namespace NPT.K4

/-! ### A permutation matrix against a PSD matrix -/

/-- `|Σ_I X (τ I) I| ≤ re (tr X)` for PSD `X` and a bijection `τ`. -/
lemma abs_sum_perm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (τ : ι → ι) (hτ : Function.Bijective τ) : ‖∑ I, X (τ I) I‖ ≤ (X.trace).re := by
  set S : ℂ := ∑ I, X (τ I) I with hS
  have htr : 0 ≤ (X.trace).re := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.1 (hX.diag_nonneg (i := i))).1
  by_cases hS0 : S = 0
  · rw [hS0, norm_zero]; exact htr
  set ω : ℂ := S / (‖S‖ : ℂ) with hω
  have hnS : (‖S‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hS0)
  have hq : ∀ I, 0 ≤ X I I - ω * X I (τ I) - star ω * X (τ I) I + ω * star ω * X (τ I) (τ I) := by
    intro I
    have h := hX.dotProduct_mulVec_nonneg
      ((Pi.single I (1 : ℂ) : ι → ℂ) - ω • (Pi.single (τ I) (1 : ℂ) : ι → ℂ))
    convert h using 1
    simp only [star_sub, star_smul, Pi.star_single, star_one, Matrix.mulVec_sub, Matrix.mulVec_smul,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, Matrix.mulVec_single_one,
      single_dotProduct, one_mul, smul_eq_mul, Matrix.col_apply]
    ring
  have hsum := Finset.sum_nonneg fun I (_ : I ∈ (univ : Finset ι)) => hq I
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
  have h1 : ∑ I, X (τ I) (τ I) = ∑ I, X I I := hτ.sum_comp (fun I => X I I)
  have hH : ∀ I J, X I J = star (X J I) := fun I J => by
    rw [← Matrix.conjTranspose_apply, hX.1.eq]
  have h2 : ∑ I, X I (τ I) = star S := by
    rw [hS, star_sum]; exact Finset.sum_congr rfl fun I _ => hH I (τ I)
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h2, h1, ← hS] at hsum
  have hSS : S * star S = (‖S‖ : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hstarn : star (‖S‖ : ℂ) = (‖S‖ : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
  have hωω : ω * star ω = 1 := by
    rw [hω, star_div₀, hstarn, div_mul_div_comm, hSS]
    field_simp
  have hωS : ω * star S = (‖S‖ : ℂ) := by
    rw [hω, div_mul_eq_mul_div, hSS]
    field_simp
  have hSω : star ω * S = (‖S‖ : ℂ) := by
    rw [hω, star_div₀, hstarn, div_mul_eq_mul_div, mul_comm (star S) S, hSS]
    field_simp
  rw [hωω, one_mul, hωS, hSω] at hsum
  have hre := (Complex.nonneg_iff.1 hsum).1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hre
  have htrace : (∑ I, X I I).re = (X.trace).re := by simp [Matrix.trace]
  rw [htrace] at hre
  linarith

/-! ### Word operators as permutation matrices -/

variable {k d : ℕ}

lemma pinvf_pf' : ∀ (p : Fin 24) (s : Fin 4), pinvf p (pf p s) = s := by decide +kernel
lemma pf_pinvf' : ∀ (p : Fin 24) (s : Fin 4), pf p (pinvf p s) = s := by decide +kernel

/-- The leg-wise action of a word on global indices. -/
def wperm (w : Fin (k + 1) → Fin 24) (J : GI (nf k d)) : GI (nf k d) := fun l => J l ∘ pinvf (w l)

lemma VW_apply (w : Fin (k + 1) → Fin 24) (I J : GI (nf k d)) :
    VW (nf k d) 0 w I J = if I = wperm w J then 1 else 0 := by
  simp only [VW, kron, SymAvg.VG0_apply, Fintype.prod_boole]
  by_cases h : I = wperm w J
  · rw [if_pos h]; exact if_pos (fun l => by rw [h]; rfl)
  · rw [if_neg h]; exact if_neg (fun hall => h (funext hall))

lemma wperm_bij (w : Fin (k + 1) → Fin 24) : Function.Bijective (wperm (k := k) (d := d) w) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun J l => J l ∘ pf (w l), fun J => ?_, fun J => ?_⟩
  · funext l s; simp only [wperm, Function.comp, pinvf_pf']
  · funext l s; simp only [wperm, Function.comp, pf_pinvf']

lemma trace_conjVW_mul (w : Fin (k + 1) → Fin 24) (X : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) :
    ((VW (nf k d) 0 w)ᴴ * X).trace = ∑ I, X (wperm w I) I := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, VW_apply]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_eq_single (wperm w I)]
  · simp
  · intro J _ hJ; simp [hJ]
  · simp

lemma norm_trace_conjVW_le (w : Fin (k + 1) → Fin 24) {X : Matrix (GI (nf k d)) (GI (nf k d)) ℂ}
    (hX : X.PosSemidef) : ‖((VW (nf k d) 0 w)ᴴ * X).trace‖ ≤ (X.trace).re := by
  rw [trace_conjVW_mul]; exact abs_sum_perm_le X hX _ (wperm_bij w)

/-! ### The word Gram matrix -/

lemma trace_VG0 (n : ℕ) [NeZero n] (p : Fin 24) : (VG ℂ n 0 p).trace = (trF n p : ℂ) := by
  have h := fixF_eq n (pinvf p)
  have hc : ((fixF n (pinvf p) : ℚ) : ℂ) = (fixF n (pinvf p) : ℂ) := by push_cast; rfl
  rw [trF, ← hc, h]
  simp only [Matrix.trace, Matrix.diag, SymAvg.VG0_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- `tr (VW vᴴ · VW w) = ∏_l gram (nf l) (v l) (w l)`. -/
lemma trace_conjVW_VW [NeZero d] (v w : Fin (k + 1) → Fin 24) :
    ((VW (nf k d) 0 v)ᴴ * VW (nf k d) 0 w).trace = ∏ l, (gram (nf k d l) (v l) (w l) : ℂ) := by
  rw [VW_conjTranspose (by norm_num), SymAvg.VW_mul0, VW, trace_kron]
  refine Finset.prod_congr rfl fun l _ => ?_
  have : NeZero (nf k d l) := ⟨by unfold nf; split_ifs <;> simp [NeZero.ne]⟩
  rw [trace_VG0]; rfl

/-! ### The generalized inverse at word level -/

/-- `gram n · (hInt n / hDen n) · gram n = gram n` for n = 2, 3, as finite sums. -/
lemma ghg_leg (n : ℕ) (hn : n = 2 ∨ n = 3) (p s : Fin 24) :
    ∑ q, ∑ r, (gram n p q : ℂ) * ((hInt n q r : ℂ) / (hDen n : ℂ)) * (gram n r s : ℂ) = (gram n p s : ℂ) := by
  have hok : ghgOK n = true := by rcases hn with rfl | rfl; exact ghg_ok2; exact ghg_ok3
  have h := List.all_eq_true.1 (List.all_eq_true.1 hok p (List.mem_finRange p)) s (List.mem_finRange s)
  rw [beq_iff_eq] at h
  have hden : (hDen n : ℂ) ≠ 0 := by rcases hn with rfl | rfl <;> simp [hDen]
  have h2 : (∑ q, gram n p q * ∑ r, hInt n q r * gram n r s : ℤ) = (hDen n : ℤ) * gram n p s := by
    rw [← h]; unfold ghg; simp only [Fin.sum_univ_def]
  have h3 := congrArg (Int.cast : ℤ → ℂ) h2
  push_cast at h3
  have hL : ∑ q, ∑ r, (gram n p q : ℂ) * ((hInt n q r : ℂ) / (hDen n : ℂ)) * (gram n r s : ℂ) =
      (∑ q, (gram n p q : ℂ) * ∑ r, (hInt n q r : ℂ) * (gram n r s : ℂ)) / (hDen n : ℂ) := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.sum_div]; refine Finset.sum_congr rfl fun r _ => ?_; ring
  rw [hL, h3, mul_div_cancel_left₀ _ hden]

/-- Leg inverse of a word pair. -/
noncomputable def Hw (w v : Fin (k + 1) → Fin 24) : ℂ :=
  ∏ l, ((hInt (nf k d l) (w l) (v l) : ℂ) / (hDen (nf k d l) : ℂ))

/-- Word Gram matrix. -/
def Gw (v w : Fin (k + 1) → Fin 24) : ℂ := ∏ l, (gram (nf k d l) (v l) (w l) : ℂ)

lemma nf_two_three (hd : d = 3) (l : Fin (k + 1)) : nf k d l = 2 ∨ nf k d l = 3 := by
  unfold nf; split_ifs
  · right; exact hd
  · left; rfl

lemma ghg_word (hd : d = 3) (w x : Fin (k + 1) → Fin 24) :
    ∑ u, ∑ v, Gw (k := k) (d := d) w u * Hw (k := k) (d := d) u v * Gw (k := k) (d := d) v x =
      Gw (k := k) (d := d) w x := by
  set F : Fin (k + 1) → Fin 24 → Fin 24 → ℂ := fun l q r =>
    (gram (nf k d l) (w l) q : ℂ) * ((hInt (nf k d l) q r : ℂ) / (hDen (nf k d l) : ℂ)) *
      (gram (nf k d l) r (x l) : ℂ) with hF
  have e1 : ∀ u v : Fin (k + 1) → Fin 24,
      Gw (k := k) (d := d) w u * Hw (k := k) (d := d) u v * Gw (k := k) (d := d) v x = ∏ l, F l (u l) (v l) := by
    intro u v; simp only [Gw, Hw, hF]; rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  have e2 : ∀ u : Fin (k + 1) → Fin 24, ∑ v : Fin (k + 1) → Fin 24, ∏ l, F l (u l) (v l) =
      ∏ l, ∑ r : Fin 24, F l (u l) r := by
    intro u; rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 24))), Fintype.piFinset_univ]
  have e3 : ∑ u : Fin (k + 1) → Fin 24, ∏ l, ∑ r : Fin 24, F l (u l) r =
      ∏ l, ∑ q : Fin 24, ∑ r : Fin 24, F l q r := by
    rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 24))), Fintype.piFinset_univ]
  simp only [e1, e2]
  rw [e3]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [hF]
  exact ghg_leg _ (nf_two_three hd l) _ _

/-! ### The bound -/

/-- `Kc k = (786/8640)^k · (496/2880)`. -/
noncomputable def Kc (k : ℕ) : ℝ := ((786 : ℝ) / 8640) ^ k * (496 / 2880)

lemma le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma rowsum_le (n : ℕ) (p : Fin 24) : ∑ q, |(hInt n p q : ℝ)| ≤ (hRowMax n : ℝ) := by
  have hle : ((List.finRange 24).map fun q => (hInt n p q).natAbs).sum ≤ hRowMax n :=
    le_foldr_max (List.mem_map.2 ⟨p, List.mem_finRange p, rfl⟩)
  have e : ∑ q, |(hInt n p q : ℝ)| =
      ((((List.finRange 24).map fun q => (hInt n p q).natAbs).sum : ℕ) : ℝ) := by
    rw [Fin.sum_univ_def, Nat.cast_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    simp [Nat.cast_natAbs]
  rw [e]; exact_mod_cast hle

lemma Hw_rowsum (hd : d = 3) (w : Fin (k + 1) → Fin 24) : ∑ v, ‖Hw (k := k) (d := d) w v‖ ≤ Kc k := by
  have e : ∑ v, ‖Hw (k := k) (d := d) w v‖ =
      ∏ l, ∑ r : Fin 24, |(hInt (nf k d l) (w l) r : ℝ)| / (hDen (nf k d l) : ℝ) := by
    rw [Finset.prod_univ_sum (fun _ => (univ : Finset (Fin 24))), Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Hw, norm_prod, norm_div, Complex.norm_intCast, Complex.norm_natCast]
  rw [e]
  have hb : ∀ l : Fin (k + 1), ∑ r : Fin 24, |(hInt (nf k d l) (w l) r : ℝ)| / (hDen (nf k d l) : ℝ) ≤
      (hRowMax (nf k d l) : ℝ) / (hDen (nf k d l) : ℝ) := by
    intro l
    rw [← Finset.sum_div]
    exact div_le_div_of_nonneg_right (rowsum_le _ _) (Nat.cast_nonneg _)
  calc ∏ l, ∑ r : Fin 24, |(hInt (nf k d l) (w l) r : ℝ)| / (hDen (nf k d l) : ℝ)
      ≤ ∏ l, (hRowMax (nf k d l) : ℝ) / (hDen (nf k d l) : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro l _; exact Finset.sum_nonneg fun r _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
        · intro l _; exact hb l
    _ = Kc k := by
        rw [Fin.prod_univ_castSucc]
        have h1 : ∀ i : Fin k, nf k d i.castSucc = 3 := fun i => by simp [nf, hd]
        have h2 : nf k d (Fin.last k) = 2 := by simp [nf]
        simp only [h1, h2, hRowMax3, hRowMax2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        unfold Kc hDen; norm_num

/-! ### The coefficients -/

/-- **Bounded coefficients of the projection onto the word span** (d = 3). -/
theorem coeff_bound (hd : d = 3) [NeZero d] {X Y : Matrix (GI (nf k d)) (GI (nf k d)) ℂ} (hX : X.PosSemidef)
    (hY : IsProj (spanS (nf := nf k d) 0) X Y) :
    ∃ c : (Fin (k + 1) → Fin 24) → ℂ, Y = ∑ w, c w • VW (nf k d) 0 w ∧ ∀ w, ‖c w‖ ≤ Kc k * (X.trace).re := by
  set g : (Fin (k + 1) → Fin 24) → ℂ := fun v => ((VW (nf k d) 0 v)ᴴ * X).trace with hg
  set c : (Fin (k + 1) → Fin 24) → ℂ := fun w => ∑ v, Hw (k := k) (d := d) w v * g v with hc
  have htr : 0 ≤ (X.trace).re := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => (Complex.nonneg_iff.1 (hX.diag_nonneg (i := i))).1
  have hgram : ∀ v w : Fin (k + 1) → Fin 24, ∀ a : ℂ,
      ((VW (nf k d) 0 v)ᴴ * (a • VW (nf k d) 0 w)).trace = a * Gw (k := k) (d := d) v w := by
    intro v w a
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_conjVW_VW, smul_eq_mul]; rfl
  refine ⟨c, ?_, fun w => ?_⟩
  · obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hY.1
    have hgY : ∀ v, g v = ∑ u, y u * Gw (k := k) (d := d) v u := by
      intro v
      have h1 := hY.2 (VW (nf k d) 0 v) (VW_mem 0 v)
      simp only [hg]
      rw [← h1, ← hy, Matrix.mul_sum, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun u _ => hgram v u (y u)
    set Z := (∑ w, c w • VW (nf k d) 0 w) - Y with hZ
    have hZorth : ∀ v, ((VW (nf k d) 0 v)ᴴ * Z).trace = 0 := by
      intro v
      rw [hZ, Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_sum, Matrix.trace_sum, hY.2 _ (VW_mem 0 v)]
      simp only [hgram]
      rw [sub_eq_zero]
      change ∑ w, c w * Gw (k := k) (d := d) v w = g v
      have e1 : ∑ w, c w * Gw (k := k) (d := d) v w =
          ∑ w, ∑ x, ∑ u, y u * (Gw (k := k) (d := d) v w * Hw (k := k) (d := d) w x * Gw (k := k) (d := d) x u) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        simp only [hc, hgY, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
      have e2 : ∑ w, ∑ x, ∑ u, y u * (Gw (k := k) (d := d) v w * Hw (k := k) (d := d) w x * Gw (k := k) (d := d) x u) =
          ∑ u, y u * ∑ w, ∑ x, Gw (k := k) (d := d) v w * Hw (k := k) (d := d) w x * Gw (k := k) (d := d) x u := by
        have e3 : ∀ w, ∑ x, ∑ u, y u * (Gw (k := k) (d := d) v w * Hw (k := k) (d := d) w x * Gw (k := k) (d := d) x u) =
            ∑ u, ∑ x, y u * (Gw (k := k) (d := d) v w * Hw (k := k) (d := d) w x * Gw (k := k) (d := d) x u) :=
          fun w => Finset.sum_comm
        simp only [e3]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum]
      rw [e1, e2, hgY v]
      exact Finset.sum_congr rfl fun u _ => by rw [ghg_word hd]
    have hZspan : Z ∈ spanS (nf := nf k d) 0 :=
      Submodule.sub_mem _ (Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (VW_mem 0 w)) hY.1
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hZspan
    have hZh : Zᴴ = ∑ u, star (z u) • (VW (nf k d) 0 u)ᴴ := by
      rw [← hz, Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun u _ => Matrix.conjTranspose_smul _ _
    have hZZ : (Zᴴ * Z).trace = 0 := by
      rw [hZh, Matrix.sum_mul, Matrix.trace_sum]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [Matrix.smul_mul, Matrix.trace_smul, hZorth u, smul_zero]
    have hZ0 : Z = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 hZZ
    rw [hZ, sub_eq_zero] at hZ0
    exact hZ0.symm
  · calc ‖c w‖ ≤ ∑ v, ‖Hw (k := k) (d := d) w v‖ * ‖g v‖ := by
          simp only [hc]
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun v _ => norm_mul _ _))
      _ ≤ ∑ v, ‖Hw (k := k) (d := d) w v‖ * (X.trace).re :=
          Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (norm_trace_conjVW_le v hX) (norm_nonneg _)
      _ = (∑ v, ‖Hw (k := k) (d := d) w v‖) * (X.trace).re := by rw [Finset.sum_mul]
      _ ≤ Kc k * (X.trace).re := mul_le_mul_of_nonneg_right (Hw_rowsum hd w) htr

end NPT.K4
