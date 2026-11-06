/-
NPT.K4.Assemble — `EP (Fin k) 3 (β/α)` from the individual checks of a slack certificate.

`ep_of_checks` combines `soundness_slack` with `classSum_of_modEq` (class sums from the mod-p checks with residual
targets), `abs_ΛS_le` (the crude bound, from data maxima) and `hslack_of_int` (the integer slack check).  Its inputs
are exactly what the data import and the checks provide:
* the certificate `C` with `C.d = 3`, `WF C`, PSD multipliers;
* classes `cls`, representatives `rep`, witnesses `wit` (conditions as in `IdFact`), a code set `codes f ∋ cls f w`;
* integer residuals `Rint f j` (bounded by `R`, `Σ_f Σ_{j ∈ codes f} |Rint f j| ≤ Ssum`) and the integer slack
  check against `nu = nuNum / nuDen`;
* data maxima `BW`, `BZ` (multiplier diagonals), `NB`, `DM`, `BJ`;
* integer word values `ZS f w = D · ΛS f w` and, for every modulus `p` of a pairwise-coprime list `ps` with
  `∏ p > 2 (D · 24^(k+1) · crudeS + R)`, the congruences `Σ_{class} ZS ≡ Rint (mod p)`.
-/
import NPT.K4.CRT

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident
open scoped ComplexOrder

namespace NPT.K4

theorem ep_of_checks (C : CertD) [NeZero C.d] (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α)
    (nuNum : ℤ) (nuDen : ℕ) (hnuDen : 0 < nuDen) (D : ℕ) (hD : 0 < D)
    (hwf : WF C) (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    (cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ) (rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24))
    (wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool)
    (hG : ∀ f < 3, ∀ w, inG f (wit f w).1 = true ∧ inG f (wit f w).2.1 = true)
    (hσ : ∀ f < 3, ∀ w, Function.Bijective (wit f w).2.2.1)
    (hrep : ∀ f < 3, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w))
    (codes : ℕ → Finset ℕ) (hcodes : ∀ f < 3, ∀ w, cls f w ∈ codes f)
    (Rint : ℕ → ℕ → ℤ) (R : ℕ) (hR : ∀ f j, |Rint f j| ≤ R) (Ssum : ℕ)
    (hS : ∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |Rint f j| ≤ Ssum)
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
    (hmod : ∀ p ∈ ps, ∀ f < 3, ∀ w₀,
      (∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ZS f w) ≡ Rint f (cls f w₀) [ZMOD p]) :
    NPT.EP (Fin C.k) C.d ((β : ℝ) / α) := by
  have hd : 2 ≤ C.d := by omega
  have hB : ∀ f w, |ΛS C α β ((nuNum : ℚ) / nuDen) f w| ≤ crudeS C α β ((nuNum : ℚ) / nuDen) DM NB BW BJ BZ :=
    fun f w => abs_ΛS_le C hd α β _ hpsd hW hBZ hZ hNB hDM hJ f w
  let hid : IdFactS C α β ((nuNum : ℚ) / nuDen) :=
    { cls := cls, rep := rep, wit := wit, hG := hG, hσ := hσ, hrep := hrep
      res := fun f j => (Rint f j : ℚ) / D
      codes := codes, hcodes := hcodes
      hsum := fun f hf w₀ => classSum_of_modEq C α β _ D hD ZS hZS _ hB R ps hcop hP (cls f) f (cls f w₀)
        (Rint f (cls f w₀)) (hR _ _) (fun p hp => hmod p hp f hf w₀) }
  exact soundness_slack C hd3 α β hα _ hwf hid hpsd
    (hslack_of_int C.k C.d D hD nuNum nuDen hnuDen codes Rint Ssum hS hchk)

/-- **`EP` from exact class sums** (native route: the slice checks give the class sums of `ZS` exactly, e.g. by
`classSum_exact_of_slices`; no CRT and no a-priori bound are needed). -/
theorem ep_of_exact (C : CertD) [NeZero C.d] (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α)
    (nuNum : ℤ) (nuDen : ℕ) (hnuDen : 0 < nuDen) (D : ℕ) (hD : 0 < D)
    (hwf : WF C) (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    (cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ) (rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24))
    (wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool)
    (hG : ∀ f < 3, ∀ w, inG f (wit f w).1 = true ∧ inG f (wit f w).2.1 = true)
    (hσ : ∀ f < 3, ∀ w, Function.Bijective (wit f w).2.2.1)
    (hrep : ∀ f < 3, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w))
    (codes : ℕ → Finset ℕ) (hcodes : ∀ f < 3, ∀ w, cls f w ∈ codes f)
    (Rint : ℕ → ℕ → ℤ) (Ssum : ℕ)
    (hS : ∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |Rint f j| ≤ Ssum)
    (hchk : (((2 * C.d ^ C.k) ^ 4 * 786 ^ C.k * 496 * Ssum * nuDen : ℕ) : ℤ) ≤
      nuNum * ((D * (8640 ^ C.k * 2880) : ℕ) : ℤ))
    (ZS : ℕ → (Fin (C.k + 1) → Fin 24) → ℤ)
    (hZS : ∀ f w, (ZS f w : ℚ) = D * ΛS C α β ((nuNum : ℚ) / nuDen) f w)
    (hex : ∀ f < 3, ∀ w₀, ∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ZS f w = Rint f (cls f w₀)) :
    NPT.EP (Fin C.k) C.d ((β : ℝ) / α) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  let hid : IdFactS C α β ((nuNum : ℚ) / nuDen) :=
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
  exact soundness_slack C hd3 α β hα _ hwf hid hpsd
    (hslack_of_int C.k C.d D hD nuNum nuDen hnuDen codes Rint Ssum hS hchk)

end NPT.K4

#print axioms NPT.K4.ep_of_checks
#print axioms NPT.K4.ep_of_exact
