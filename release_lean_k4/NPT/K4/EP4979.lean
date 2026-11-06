/-
NPT.K4.EP4979 — `EP (Fin 4) 3 (4979/10000)` from the five-family checks (the α ≥ −0.4979 certificate).

`ep4979_of_slicesB` is `ep497_of_slicesB` for five families: `soundness_slack5` with the kernel-checked five-family data of
`NPT.K4.D3T4979` (`wf5_cert` through `wfCheck5_sound`, PSD), the five-family class data of `NPT.K4.Classes.WitAll5`
(families 31/22/13 as for K4@497, families 40/04 one shared S_4 data set; read slice by slice, `clsW5_slices`), the
route's class sums (`NPT.K4.Route.hsum_of_slicesB`, family-generic), the keys (`key_all`), residuals at the
representatives (`RintOf`) and the integer slack check over five families (`hslack_of_int5`).  The route data and
checks and the residual lists are the hypotheses; the final file instantiates them.
-/
import NPT.K4.Assemble5
import NPT.K4.ClsSlicesW
import NPT.K4.ClsLen3
import NPT.K4.Classes.WitAll5
import NPT.K4.Route.HsumSB
import NPT.K4.RouteKeys
import NPT.K4.D3T4979.WF

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.K4 NPT.K4.Classes
open scoped ComplexOrder

namespace NPT.K4.D3T4979

/-- Common denominator of the five-family import: `2^254·10000^4·162^4`. -/
def D5 : ℕ := 2 ^ 254 * 10000 ^ 4 * 162 ^ 4

theorem D5_pos : 0 < D5 := by unfold D5; positivity

theorem nuDen5_pos : 0 < nuDen := by decide +kernel

instance : NeZero cert.d := ⟨by decide⟩

/-- Slice lists of the five families (31/22/13 from the K4@497 class data, 40/04 the shared S_4 data). -/
def slicesL5 (f : ℕ) : List (List ℕ) := if f < 3 then NPT.K4.D3T497.slicesL f else slices3

theorem slicesL5_length (f : ℕ) (_hf : f < 5) : (slicesL5 f).length = 24 := by
  unfold slicesL5
  split_ifs with h
  · exact NPT.K4.D3T497.slicesL_length f h
  · exact slices3_length

theorem slicesL5_len (f : ℕ) (_hf : f < 5) : ∀ l ∈ slicesL5 f, l.length = 331776 := by
  unfold slicesL5
  split_ifs with h
  · exact NPT.K4.D3T497.slicesL_len f h
  · exact slices3_len

/-- **The class of a word, slice by slice, five families.** -/
theorem clsW5_slices (f : ℕ) (_hf : f < 5) (w : Fin 5 → Fin 24) :
    clsW5 f w = Route.cls5 (fun j => (slicesL5 f).getD j []) w := by
  by_cases h3 : f < 3
  · have e1 : clsW5 f w = clsW f w := by
      show (clsL5 f).getD (posW5 w) 0 = (clsL f).getD (posW5 w) 0
      rw [show clsL5 f = clsL f from ite_eq_left h3]
    rw [e1, NPT.K4.D3T497.clsW_slices f h3 w, show slicesL5 f = NPT.K4.D3T497.slicesL f from ite_eq_left h3]
  · have e1 : clsW5 f w = cls3.getD (posW5 w) 0 := by
      show (clsL5 f).getD (posW5 w) 0 = cls3.getD (posW5 w) 0
      rw [show clsL5 f = cls3 from ite_eq_right h3]
    rw [e1, cls3_flatten, cls_bridge slices3 slices3_length slices3_len w, show slicesL5 f = slices3 from ite_eq_right h3]

theorem ep4979_of_slicesB (gsF : ℕ → List GrpF) (t0F : ℕ → AT) (offsF : ℕ → ℕ → List (ℕ × ℤ))
    (b E0 : ℕ) (cG cO cT cE : ℤ)
    (hG : ∀ f < 5, ∀ G ∈ gsF f, Route.grpOK5 cert E0 G = true)
    (hperm : ∀ f < 5, ((gsF f).flatMap fun G => itemsOf G.tree).Perm (allItems cert f))
    (hcG : (cG : ℚ) * 2 ^ E0 = -(D5 : ℚ))
    (hcO : (cO : ℚ) = (D5 : ℚ) / ((10000 : ℚ) ^ 4 * (2 * 3 ^ 4) ^ 4))
    (hcT : (cT : ℚ) = -((D5 : ℚ) * (((nuNum : ℤ) : ℚ) / nuDen) / (2 * 3 ^ 4) ^ 4))
    (hcE : (cE : ℚ) = (D5 : ℚ) / ((2 * Lden : ℕ) : ℚ))
    (hkind : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (4 + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf 4 3 l = 2)
    (hchk : ∀ f < 5, ∀ j : Fin 24, Route.sliceCheck b (Route.parts5B cert 10000 4979 cG cO cT cE f (gsF f) j)
      ((slicesL5 f).getD j.val []) (Route.tOff (t0F f) (offsF f j.val)) = true)
    (reps : ℕ → List ℕ) (resL : ℕ → List ℤ)
    (hkeys : ∀ f < 5, ∀ e ∈ (t0F f).leaves, e.1 ∈ reps f)
    (hoff : ∀ f < 5, ∀ c ∈ reps f,
      ∑ j : Fin 24, Route.offAt (Route.tOff (t0F f) (offsF f j.val)) c = -RintOf (reps f) (resL f) c)
    (Ssum : ℕ)
    (hSsum : ((resL 0).map Int.natAbs).sum + ((resL 1).map Int.natAbs).sum + ((resL 2).map Int.natAbs).sum +
      ((resL 3).map Int.natAbs).sum + ((resL 4).map Int.natAbs).sum ≤ Ssum)
    (hchk2 : (((2 * 3 ^ 4) ^ 4 * 786 ^ 4 * 496 * Ssum * nuDen : ℕ) : ℤ) ≤
      (nuNum : ℤ) * ((D5 * (8640 ^ 4 * 2880) : ℕ) : ℤ)) :
    NPT.EP (Fin 4) 3 (4979 / 10000) := by
  have hDq : (D5 : ℚ) ≠ 0 := by exact_mod_cast D5_pos.ne'
  set nu : ℚ := ((nuNum : ℤ) : ℚ) / nuDen with hnu
  -- class sums of ΛS from the slice checks
  have hsum : ∀ f < 5, ∀ w₀ : Fin 5 → Fin 24,
      ∑ w ∈ univ.filter (fun w => clsW5 f w = clsW5 f w₀), ΛS cert 10000 4979 nu f w =
        (RintOf (reps f) (resL f) (clsW5 f w₀) : ℚ) / D5 := by
    intro f hf w₀
    set cl : List ℕ := (slicesL5 f).getD (w₀ 4).val [] with hcl
    set q : ℕ := posW (Fin.init w₀) with hq_def
    have hc : clsW5 f w₀ = cl.getD q 0 := by rw [clsW5_slices f hf w₀]; rfl
    have hq : q < cl.length := by
      have hmem : cl ∈ slicesL5 f :=
        getD_mem_of_lt _ _ [] (by rw [slicesL5_length f hf]; exact (w₀ 4).isLt)
      rw [slicesL5_len f hf cl hmem]
      exact posW_init_lt w₀
    have hkey : ∀ j : Fin 24, ((Route.tOff (t0F f) (offsF f j.val)).leaves.getD
        ((Route.tOff (t0F f) (offsF f j.val)).tgt (clsW5 f w₀)) dLeaf).1 = clsW5 f w₀ := by
      intro j
      rw [hc]
      exact Route.key_all b _ cl (t0F f) (offsF f (w₀ 4).val) (offsF f j.val) (hchk f hf (w₀ 4)) q hq
    have hmem : clsW5 f w₀ ∈ reps f := by
      have h0 := Route.key_all b _ cl (t0F f) (offsF f (w₀ 4).val) [] (hchk f hf (w₀ 4)) q hq
      have ht : Route.tOff (t0F f) [] = t0F f := rfl
      rw [ht] at h0
      obtain ⟨e, he, he1⟩ := Route.key_mem (t0F f) _ h0
      rw [hc, ← he1]
      exact hkeys f hf e he
    have h := Route.hsum_of_slicesB 3 types mods eqs blocks Lden (2 * Lden) rfl 10000 4979 (by norm_num) nu E0
      cG cO cT cE (D5 : ℚ) hDq f (gsF f) (hG f hf) (hperm f hf) hcG hcO hcT hcE hkind
      b (fun j => (slicesL5 f).getD j []) (fun j => Route.tOff (t0F f) (offsF f j)) (hchk f hf) (clsW5 f w₀) hkey
      (RintOf (reps f) (resL f) (clsW5 f w₀)) (hoff f hf _ hmem)
    have e : (univ.filter (fun w : Fin 5 → Fin 24 => clsW5 f w = clsW5 f w₀)) =
        univ.filter (fun w : Fin (4 + 1) → Fin 24 =>
          Route.cls5 (fun j => (slicesL5 f).getD j []) w = clsW5 f w₀) :=
      Finset.filter_congr fun w _ => by rw [clsW5_slices f hf w]
    rw [e]
    exact h
  -- the identity fact with residuals, five families
  let hid : IdFactS5 cert 10000 4979 nu :=
    { cls := clsW5, rep := repW5, wit := witW5, hG := hG5', hσ := hσ5', hrep := hrep5'
      res := fun f j => (RintOf (reps f) (resL f) j : ℚ) / D5
      codes := fun _ => Finset.range (24 * slen5), hcodes := hcodes5'
      hsum := fun f hf w₀ => hsum f hf w₀ }
  -- the slack
  have hS : ∑ f ∈ Finset.range 5, ∑ j ∈ Finset.range (24 * slen5), |RintOf (reps f) (resL f) j| ≤ Ssum := by
    have h0 := resMass_reps_le (reps 0) (resL 0) (24 * slen5)
    have h1 := resMass_reps_le (reps 1) (resL 1) (24 * slen5)
    have h2 := resMass_reps_le (reps 2) (resL 2) (24 * slen5)
    have h3 := resMass_reps_le (reps 3) (resL 3) (24 * slen5)
    have h4 := resMass_reps_le (reps 4) (resL 4) (24 * slen5)
    have hS' : ((((resL 0).map Int.natAbs).sum + ((resL 1).map Int.natAbs).sum + ((resL 2).map Int.natAbs).sum +
        ((resL 3).map Int.natAbs).sum + ((resL 4).map Int.natAbs).sum : ℕ) : ℤ) ≤ Ssum := by exact_mod_cast hSsum
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add] at hS'
    linarith
  have hsl := hslack_of_int5 4 3 D5 D5_pos (nuNum : ℤ) nuDen nuDen5_pos (fun _ => Finset.range (24 * slen5))
    (fun f j => RintOf (reps f) (resL f) j) Ssum hS hchk2
  have hEP := soundness_slack5 cert rfl 10000 4979 (by norm_num) nu (wfCheck5_sound wf5_cert) hid
    (blkZ_psd_of blocks_psd) hsl
  have hcast : ((4979 : ℕ) : ℝ) / ((10000 : ℕ) : ℝ) = 4979 / 10000 := by norm_num
  rw [hcast] at hEP
  exact hEP

end NPT.K4.D3T4979

#print axioms NPT.K4.D3T4979.ep4979_of_slicesB
