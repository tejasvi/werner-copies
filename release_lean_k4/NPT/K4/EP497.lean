/-
NPT.K4.EP497 — `EP (Fin 4) 3 (497/1000)` from the K4@497 checks.

`ep497_of_slicesB` combines `soundness_slack` with the kernel-checked data of `NPT.K4.D3T497` (WF, PSD), the class
data of `NPT.K4.Classes.WitAll` (read slice by slice, `clsW_slices`), the route's class sums
(`NPT.K4.Route.hsum_of_slicesB`, parts with λ-boxes), residuals stored at the representatives (`RintOf`) and the
integer slack check (`hslack_of_int`).  Keys: a class code of a word is found in its own slice, so the slice check
makes it a key of the common accumulator tree (`key_all`), hence one of the representatives (`hkeys`), whose offsets
are checked (`hoff`).  The route data and checks and the residual lists are the hypotheses; the final file
instantiates them.
-/
import NPT.K4.Assemble
import NPT.K4.ClsSlicesW
import NPT.K4.Route.HsumSB
import NPT.K4.RouteKeys
import NPT.K4.D3T497.WF
import NPT.K4.D3T497.Consts

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.K4 NPT.K4.Classes
open scoped ComplexOrder

namespace NPT.K4.D3T497

instance : NeZero cert.d := ⟨by decide⟩

theorem ep497_of_slicesB (gsF : ℕ → List GrpF) (t0F : ℕ → AT) (offsF : ℕ → ℕ → List (ℕ × ℤ))
    (b E0 : ℕ) (cG cO cT cE : ℤ)
    (hG : ∀ f < 3, ∀ G ∈ gsF f, Route.grpOK5 cert E0 G = true)
    (hperm : ∀ f < 3, ((gsF f).flatMap fun G => itemsOf G.tree).Perm (allItems cert f))
    (hcG : (cG : ℚ) * 2 ^ E0 = -(D : ℚ))
    (hcO : (cO : ℚ) = (D : ℚ) / ((1000 : ℚ) ^ 4 * (2 * 3 ^ 4) ^ 4))
    (hcT : (cT : ℚ) = -((D : ℚ) * (((nuNum : ℤ) : ℚ) / nuDen) / (2 * 3 ^ 4) ^ 4))
    (hcE : (cE : ℚ) = (D : ℚ) / ((2 * Lden : ℕ) : ℚ))
    (hkind : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (4 + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf 4 3 l = 2)
    (hchk : ∀ f < 3, ∀ j : Fin 24, Route.sliceCheck b (Route.parts5B cert 1000 497 cG cO cT cE f (gsF f) j)
      ((slicesL f).getD j.val []) (Route.tOff (t0F f) (offsF f j.val)) = true)
    (reps : ℕ → List ℕ) (resL : ℕ → List ℤ)
    (hkeys : ∀ f < 3, ∀ e ∈ (t0F f).leaves, e.1 ∈ reps f)
    (hoff : ∀ f < 3, ∀ c ∈ reps f,
      ∑ j : Fin 24, Route.offAt (Route.tOff (t0F f) (offsF f j.val)) c = -RintOf (reps f) (resL f) c)
    (Ssum : ℕ)
    (hSsum : ((resL 0).map Int.natAbs).sum + ((resL 1).map Int.natAbs).sum + ((resL 2).map Int.natAbs).sum ≤ Ssum)
    (hchk2 : (((2 * 3 ^ 4) ^ 4 * 786 ^ 4 * 496 * Ssum * nuDen : ℕ) : ℤ) ≤
      (nuNum : ℤ) * ((D * (8640 ^ 4 * 2880) : ℕ) : ℤ)) :
    NPT.EP (Fin 4) 3 (497 / 1000) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast D_pos.ne'
  set nu : ℚ := ((nuNum : ℤ) : ℚ) / nuDen with hnu
  -- class sums of ΛS from the slice checks
  have hsum : ∀ f < 3, ∀ w₀ : Fin 5 → Fin 24,
      ∑ w ∈ univ.filter (fun w => clsW f w = clsW f w₀), ΛS cert 1000 497 nu f w =
        (RintOf (reps f) (resL f) (clsW f w₀) : ℚ) / D := by
    intro f hf w₀
    set cl : List ℕ := (slicesL f).getD (w₀ 4).val [] with hcl
    set q : ℕ := posW (Fin.init w₀) with hq_def
    have hc : clsW f w₀ = cl.getD q 0 := by rw [clsW_slices f hf w₀]; rfl
    have hq : q < cl.length := by
      have hmem : cl ∈ slicesL f :=
        getD_mem_of_lt _ _ [] (by rw [slicesL_length f hf]; exact (w₀ 4).isLt)
      rw [slicesL_len f hf cl hmem]
      exact posW_init_lt w₀
    have hkey : ∀ j : Fin 24, ((Route.tOff (t0F f) (offsF f j.val)).leaves.getD
        ((Route.tOff (t0F f) (offsF f j.val)).tgt (clsW f w₀)) dLeaf).1 = clsW f w₀ := by
      intro j
      rw [hc]
      exact Route.key_all b _ cl (t0F f) (offsF f (w₀ 4).val) (offsF f j.val) (hchk f hf (w₀ 4)) q hq
    have hmem : clsW f w₀ ∈ reps f := by
      have h0 := Route.key_all b _ cl (t0F f) (offsF f (w₀ 4).val) [] (hchk f hf (w₀ 4)) q hq
      have ht : Route.tOff (t0F f) [] = t0F f := rfl
      rw [ht] at h0
      obtain ⟨e, he, he1⟩ := Route.key_mem (t0F f) _ h0
      rw [hc, ← he1]
      exact hkeys f hf e he
    have h := Route.hsum_of_slicesB 3 types mods eqs blocks Lden (2 * Lden) rfl 1000 497 (by norm_num) nu E0
      cG cO cT cE (D : ℚ) hDq f (gsF f) (hG f hf) (hperm f hf) hcG hcO hcT hcE hkind
      b (fun j => (slicesL f).getD j []) (fun j => Route.tOff (t0F f) (offsF f j)) (hchk f hf) (clsW f w₀) hkey
      (RintOf (reps f) (resL f) (clsW f w₀)) (hoff f hf _ hmem)
    have e : (univ.filter (fun w : Fin 5 → Fin 24 => clsW f w = clsW f w₀)) =
        univ.filter (fun w : Fin (4 + 1) → Fin 24 =>
          Route.cls5 (fun j => (slicesL f).getD j []) w = clsW f w₀) :=
      Finset.filter_congr fun w _ => by rw [clsW_slices f hf w]
    rw [e]
    exact h
  -- the identity fact with residuals
  let hid : IdFactS cert 1000 497 nu :=
    { cls := clsW, rep := repW, wit := witW, hG := hG5, hσ := hσ5, hrep := hrep5
      res := fun f j => (RintOf (reps f) (resL f) j : ℚ) / D
      codes := fun _ => Finset.range (24 * slen5), hcodes := hcodes5
      hsum := fun f hf w₀ => hsum f hf w₀ }
  -- the slack
  have hS : ∑ f ∈ Finset.range 3, ∑ j ∈ Finset.range (24 * slen5), |RintOf (reps f) (resL f) j| ≤ Ssum := by
    have h0 := resMass_reps_le (reps 0) (resL 0) (24 * slen5)
    have h1 := resMass_reps_le (reps 1) (resL 1) (24 * slen5)
    have h2 := resMass_reps_le (reps 2) (resL 2) (24 * slen5)
    have hS' : ((((resL 0).map Int.natAbs).sum + ((resL 1).map Int.natAbs).sum +
        ((resL 2).map Int.natAbs).sum : ℕ) : ℤ) ≤ Ssum := by exact_mod_cast hSsum
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [Nat.cast_add, Nat.cast_add] at hS'
    linarith
  have hsl := hslack_of_int 4 3 D D_pos (nuNum : ℤ) nuDen nuDen_pos (fun _ => Finset.range (24 * slen5))
    (fun f j => RintOf (reps f) (resL f) j) Ssum hS hchk2
  have hEP := soundness_slack cert rfl 1000 497 (by norm_num) nu (wfCheck_sound wf_cert) hid
    (blkZ_psd_of blocks_psd) hsl
  have hcast : ((497 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) = 497 / 1000 := by norm_num
  rw [hcast] at hEP
  exact hEP

end NPT.K4.D3T497

#print axioms NPT.K4.D3T497.ep497_of_slicesB
