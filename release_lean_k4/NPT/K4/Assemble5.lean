/-
NPT.K4.Assemble5 — `EP (Fin k) 3 (β/α)` from the checks of a five-family slack certificate (five-family certificate):
`ep_of_exact5` (exact class sums, native route) and `ep_of_checks5` (mod-p class sums with residual targets and the
crude bound, kernel route), as `ep_of_exact` / `ep_of_checks` with `soundness_slack5`, `IdFactS5` (`f < 5`, family
groups `inG5`) and the slack sum over five families (`hslack_of_int5`).
-/
import NPT.K4.SoundS5
import NPT.K4.Assemble

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident
open scoped ComplexOrder

namespace NPT.K4

/-- The slack inequality from one integer check, five families. -/
theorem hslack_of_int5 (k d D : ℕ) (hD : 0 < D) (nuNum : ℤ) (nuDen : ℕ) (hnuDen : 0 < nuDen)
    (codes : ℕ → Finset ℕ) (Rint : ℕ → ℕ → ℤ) (Ssum : ℕ)
    (hS : ∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |Rint f j| ≤ Ssum)
    (hchk : (((2 * d ^ k) ^ 4 * 786 ^ k * 496 * Ssum * nuDen : ℕ) : ℤ) ≤ nuNum * ((D * (8640 ^ k * 2880) : ℕ) : ℤ)) :
    (2 * (d : ℚ) ^ k) ^ 4 * Kq k * ∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |(Rint f j : ℚ) / D| ≤
      (nuNum : ℚ) / nuDen := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hnq : (0 : ℚ) < nuDen := by exact_mod_cast hnuDen
  have hsum : ∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |(Rint f j : ℚ) / D| =
      ((∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |Rint f j| : ℤ) : ℚ) / D := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_div, Nat.abs_cast]
  have hT : ((∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |Rint f j| : ℤ) : ℚ) ≤ Ssum := by exact_mod_cast hS
  have hK : Kq k = (786 : ℚ) ^ k * 496 / ((8640 : ℚ) ^ k * 2880) := by
    unfold Kq; rw [div_pow]; ring
  have hchk' : ((2 * (d : ℚ) ^ k) ^ 4 * 786 ^ k * 496 * Ssum) * nuDen ≤ nuNum * ((8640 : ℚ) ^ k * 2880 * D) := by
    have h := (Int.cast_le (R := ℚ)).2 hchk
    push_cast at h
    convert h using 1
    ring
  rw [hsum, hK]
  have hpos : (0 : ℚ) < (8640 : ℚ) ^ k * 2880 * D := by positivity
  calc (2 * (d : ℚ) ^ k) ^ 4 * ((786 : ℚ) ^ k * 496 / ((8640 : ℚ) ^ k * 2880)) *
        (((∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |Rint f j| : ℤ) : ℚ) / D)
      ≤ (2 * (d : ℚ) ^ k) ^ 4 * ((786 : ℚ) ^ k * 496 / ((8640 : ℚ) ^ k * 2880)) * ((Ssum : ℚ) / D) := by
        gcongr
    _ = ((2 * (d : ℚ) ^ k) ^ 4 * 786 ^ k * 496 * Ssum) / ((8640 : ℚ) ^ k * 2880 * D) := by
        field_simp
    _ ≤ (nuNum : ℚ) / nuDen := by
        rw [div_le_div_iff₀ hpos hnq]
        exact hchk'

/-- **`EP` from exact class sums, five families** (native route). -/
theorem ep_of_exact5 (C : CertD) [NeZero C.d] (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α)
    (nuNum : ℤ) (nuDen : ℕ) (hnuDen : 0 < nuDen) (D : ℕ) (hD : 0 < D)
    (hwf : WF5 C) (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    (cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ) (rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24))
    (wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool)
    (hG : ∀ f < 5, ∀ w, inG5 f (wit f w).1 = true ∧ inG5 f (wit f w).2.1 = true)
    (hσ : ∀ f < 5, ∀ w, Function.Bijective (wit f w).2.2.1)
    (hrep : ∀ f < 5, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w))
    (codes : ℕ → Finset ℕ) (hcodes : ∀ f < 5, ∀ w, cls f w ∈ codes f)
    (Rint : ℕ → ℕ → ℤ) (Ssum : ℕ)
    (hS : ∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |Rint f j| ≤ Ssum)
    (hchk : (((2 * C.d ^ C.k) ^ 4 * 786 ^ C.k * 496 * Ssum * nuDen : ℕ) : ℤ) ≤
      nuNum * ((D * (8640 ^ C.k * 2880) : ℕ) : ℤ))
    (ZS : ℕ → (Fin (C.k + 1) → Fin 24) → ℤ)
    (hZS : ∀ f w, (ZS f w : ℚ) = D * ΛS C α β ((nuNum : ℚ) / nuDen) f w)
    (hex : ∀ f < 5, ∀ w₀, ∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ZS f w = Rint f (cls f w₀)) :
    NPT.EP (Fin C.k) C.d ((β : ℝ) / α) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  let hid : IdFactS5 C α β ((nuNum : ℚ) / nuDen) :=
    { cls := cls, rep := rep, wit := wit, hG := hG, hσ := hσ, hrep := hrep
      res := fun f j => (Rint f j : ℚ) / D
      codes := codes, hcodes := hcodes
      hsum := fun f hf w₀ => by
        show ∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ΛS C α β ((nuNum : ℚ) / nuDen) f w =
          (Rint f (cls f w₀) : ℚ) / D
        have h := congrArg (fun z : ℤ => (z : ℚ)) (hex f hf w₀)
        simp only [Int.cast_sum, hZS, ← Finset.mul_sum] at h
        rw [eq_div_iff hDq, mul_comm]
        exact h }
  exact soundness_slack5 C hd3 α β hα _ hwf hid hpsd
    (hslack_of_int5 C.k C.d D hD nuNum nuDen hnuDen codes Rint Ssum hS hchk)

/-- **`EP` from mod-p checks with residual targets, five families** (kernel route). -/
theorem ep_of_checks5 (C : CertD) [NeZero C.d] (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α)
    (nuNum : ℤ) (nuDen : ℕ) (hnuDen : 0 < nuDen) (D : ℕ) (hD : 0 < D)
    (hwf : WF5 C) (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    (cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ) (rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24))
    (wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool)
    (hG : ∀ f < 5, ∀ w, inG5 f (wit f w).1 = true ∧ inG5 f (wit f w).2.1 = true)
    (hσ : ∀ f < 5, ∀ w, Function.Bijective (wit f w).2.2.1)
    (hrep : ∀ f < 5, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w))
    (codes : ℕ → Finset ℕ) (hcodes : ∀ f < 5, ∀ w, cls f w ∈ codes f)
    (Rint : ℕ → ℕ → ℤ) (R : ℕ) (hR : ∀ f j, |Rint f j| ≤ R) (Ssum : ℕ)
    (hS : ∑ f ∈ Finset.range 5, ∑ j ∈ codes f, |Rint f j| ≤ Ssum)
    (hchk : (((2 * C.d ^ C.k) ^ 4 * 786 ^ C.k * 496 * Ssum * nuDen : ℕ) : ℤ) ≤
      nuNum * ((D * (8640 ^ C.k * 2880) : ℕ) : ℤ))
    (BW : ℕ) (hW : ∀ t ∈ C.types, ∀ i j, |(t.W.getD i []).getD j 0| ≤ (BW : ℤ))
    (BZ : ℚ) (hBZ : 0 ≤ BZ) (hZ : ∀ t ∈ C.types, ∀ a < (C.blkZ t).n, CertD.zq (C.blkZ t) C.Lden a a ≤ BZ)
    (NB DM BJ : ℕ) (hNB : ∀ t ∈ C.types, (C.blkZ t).n ≤ NB) (hDM : ∀ t ∈ C.types, ∀ l, C.tdim t l ≤ DM)
    (hJ : maxJall C ≤ BJ)
    (ZS : ℕ → (Fin (C.k + 1) → Fin 24) → ℤ)
    (hZS : ∀ f w, (ZS f w : ℚ) = D * ΛS C α β ((nuNum : ℚ) / nuDen) f w)
    (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
    (hP : 2 * ((D : ℚ) * 24 ^ (C.k + 1) * crudeS C α β ((nuNum : ℚ) / nuDen) DM NB BW BJ BZ + R) < ps.prod)
    (hmod : ∀ p ∈ ps, ∀ f < 5, ∀ w₀,
      (∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ZS f w) ≡ Rint f (cls f w₀) [ZMOD p]) :
    NPT.EP (Fin C.k) C.d ((β : ℝ) / α) := by
  have hd : 2 ≤ C.d := by omega
  have hB : ∀ f w, |ΛS C α β ((nuNum : ℚ) / nuDen) f w| ≤ crudeS C α β ((nuNum : ℚ) / nuDen) DM NB BW BJ BZ :=
    fun f w => abs_ΛS_le C hd α β _ hpsd hW hBZ hZ hNB hDM hJ f w
  let hid : IdFactS5 C α β ((nuNum : ℚ) / nuDen) :=
    { cls := cls, rep := rep, wit := wit, hG := hG, hσ := hσ, hrep := hrep
      res := fun f j => (Rint f j : ℚ) / D
      codes := codes, hcodes := hcodes
      hsum := fun f hf w₀ => classSum_of_modEq C α β _ D hD ZS hZS _ hB R ps hcop hP (cls f) f (cls f w₀)
        (Rint f (cls f w₀)) (hR _ _) (fun p hp => hmod p hp f hf w₀) }
  exact soundness_slack5 C hd3 α β hα _ hwf hid hpsd
    (hslack_of_int5 C.k C.d D hD nuNum nuDen hnuDen codes Rint Ssum hS hchk)

end NPT.K4

#print axioms NPT.K4.ep_of_exact5
#print axioms NPT.K4.ep_of_checks5
