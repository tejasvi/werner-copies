/-
NPT.K4.Final497 — **`EP (Fin 4) 3 (497/1000)`** (native slice checks).

`ep497_of_slicesB` instantiated with the route data of `NPT.K4.Route.T497` (rule groups `rgs<f>`, accumulator trees
`t0_<f>` with the offsets `offsLK<f>`, representatives `reps<f>`, residuals `resL<f>`, constants `bP`, `E0`, `cG`,
`cO`, `cT`, `cE`), the data checks (`DataK497`, kernel), the key lists (`Keys497`, kernel), the 72 slice checks
`sliceOK<f>_<j>` (native evaluation), the offset sums `hoffK<f>_all` (kernel) and the integer slack check (kernel).
-/
import NPT.K4.EP497
import NPT.K4.Keys497
import NPT.K4.DataK497
import NPT.K4.Route.T497.HoffK0
import NPT.K4.Route.T497.Chk0_0
import NPT.K4.Route.T497.Chk0_1
import NPT.K4.Route.T497.Chk0_2
import NPT.K4.Route.T497.Chk0_3
import NPT.K4.Route.T497.Chk0_4
import NPT.K4.Route.T497.Chk0_5
import NPT.K4.Route.T497.Chk0_6
import NPT.K4.Route.T497.Chk0_7
import NPT.K4.Route.T497.Chk0_8
import NPT.K4.Route.T497.Chk0_9
import NPT.K4.Route.T497.Chk0_10
import NPT.K4.Route.T497.Chk0_11
import NPT.K4.Route.T497.Chk0_12
import NPT.K4.Route.T497.Chk0_13
import NPT.K4.Route.T497.Chk0_14
import NPT.K4.Route.T497.Chk0_15
import NPT.K4.Route.T497.Chk0_16
import NPT.K4.Route.T497.Chk0_17
import NPT.K4.Route.T497.Chk0_18
import NPT.K4.Route.T497.Chk0_19
import NPT.K4.Route.T497.Chk0_20
import NPT.K4.Route.T497.Chk0_21
import NPT.K4.Route.T497.Chk0_22
import NPT.K4.Route.T497.Chk0_23
import NPT.K4.Route.T497.HoffK1
import NPT.K4.Route.T497.Chk1_0
import NPT.K4.Route.T497.Chk1_1
import NPT.K4.Route.T497.Chk1_2
import NPT.K4.Route.T497.Chk1_3
import NPT.K4.Route.T497.Chk1_4
import NPT.K4.Route.T497.Chk1_5
import NPT.K4.Route.T497.Chk1_6
import NPT.K4.Route.T497.Chk1_7
import NPT.K4.Route.T497.Chk1_8
import NPT.K4.Route.T497.Chk1_9
import NPT.K4.Route.T497.Chk1_10
import NPT.K4.Route.T497.Chk1_11
import NPT.K4.Route.T497.Chk1_12
import NPT.K4.Route.T497.Chk1_13
import NPT.K4.Route.T497.Chk1_14
import NPT.K4.Route.T497.Chk1_15
import NPT.K4.Route.T497.Chk1_16
import NPT.K4.Route.T497.Chk1_17
import NPT.K4.Route.T497.Chk1_18
import NPT.K4.Route.T497.Chk1_19
import NPT.K4.Route.T497.Chk1_20
import NPT.K4.Route.T497.Chk1_21
import NPT.K4.Route.T497.Chk1_22
import NPT.K4.Route.T497.Chk1_23
import NPT.K4.Route.T497.HoffK2
import NPT.K4.Route.T497.Chk2_0
import NPT.K4.Route.T497.Chk2_1
import NPT.K4.Route.T497.Chk2_2
import NPT.K4.Route.T497.Chk2_3
import NPT.K4.Route.T497.Chk2_4
import NPT.K4.Route.T497.Chk2_5
import NPT.K4.Route.T497.Chk2_6
import NPT.K4.Route.T497.Chk2_7
import NPT.K4.Route.T497.Chk2_8
import NPT.K4.Route.T497.Chk2_9
import NPT.K4.Route.T497.Chk2_10
import NPT.K4.Route.T497.Chk2_11
import NPT.K4.Route.T497.Chk2_12
import NPT.K4.Route.T497.Chk2_13
import NPT.K4.Route.T497.Chk2_14
import NPT.K4.Route.T497.Chk2_15
import NPT.K4.Route.T497.Chk2_16
import NPT.K4.Route.T497.Chk2_17
import NPT.K4.Route.T497.Chk2_18
import NPT.K4.Route.T497.Chk2_19
import NPT.K4.Route.T497.Chk2_20
import NPT.K4.Route.T497.Chk2_21
import NPT.K4.Route.T497.Chk2_22
import NPT.K4.Route.T497.Chk2_23

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.K4 NPT.K4.Route.T497

namespace NPT.K4.D3T497

theorem sliceAll0 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 1000 497 cG cO cT cE 0 rgs0 j)
    ((slicesL 0).getD j.val []) (Route.tOff t0_0 (offsLK0.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK0_0, sliceOK0_1, sliceOK0_2, sliceOK0_3, sliceOK0_4, sliceOK0_5, sliceOK0_6, sliceOK0_7, sliceOK0_8, sliceOK0_9, sliceOK0_10, sliceOK0_11, sliceOK0_12, sliceOK0_13, sliceOK0_14, sliceOK0_15, sliceOK0_16, sliceOK0_17, sliceOK0_18, sliceOK0_19, sliceOK0_20, sliceOK0_21, sliceOK0_22, sliceOK0_23]

theorem sliceAll1 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 1000 497 cG cO cT cE 1 rgs1 j)
    ((slicesL 1).getD j.val []) (Route.tOff t0_1 (offsLK1.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK1_0, sliceOK1_1, sliceOK1_2, sliceOK1_3, sliceOK1_4, sliceOK1_5, sliceOK1_6, sliceOK1_7, sliceOK1_8, sliceOK1_9, sliceOK1_10, sliceOK1_11, sliceOK1_12, sliceOK1_13, sliceOK1_14, sliceOK1_15, sliceOK1_16, sliceOK1_17, sliceOK1_18, sliceOK1_19, sliceOK1_20, sliceOK1_21, sliceOK1_22, sliceOK1_23]

theorem sliceAll2 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 1000 497 cG cO cT cE 2 rgs2 j)
    ((slicesL 2).getD j.val []) (Route.tOff t0_2 (offsLK2.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK2_0, sliceOK2_1, sliceOK2_2, sliceOK2_3, sliceOK2_4, sliceOK2_5, sliceOK2_6, sliceOK2_7, sliceOK2_8, sliceOK2_9, sliceOK2_10, sliceOK2_11, sliceOK2_12, sliceOK2_13, sliceOK2_14, sliceOK2_15, sliceOK2_16, sliceOK2_17, sliceOK2_18, sliceOK2_19, sliceOK2_20, sliceOK2_21, sliceOK2_22, sliceOK2_23]

/-- The residual lists by family (a constant, so the mass bound below is syntactic). -/
def resLF (f : ℕ) : List ℤ := if f = 0 then resL0 else if f = 1 then resL1 else resL2

/-- **The endpoint property of the K4 qutrit problem at t = 497/1000.** -/
theorem EP_K4_497 : NPT.EP (Fin 4) 3 (497 / 1000) := by
  refine ep497_of_slicesB (fun f => if f = 0 then rgs0 else if f = 1 then rgs1 else rgs2)
    (fun f => if f = 0 then t0_0 else if f = 1 then t0_1 else t0_2)
    (fun f j => (if f = 0 then offsLK0 else if f = 1 then offsLK1 else offsLK2).getD j [])
    bP E0 cG cO cT cE ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun f => if f = 0 then reps0 else if f = 1 then reps1 else reps2) resLF ?_ ?_
    (((resLF 0).map Int.natAbs).sum + ((resLF 1).map Int.natAbs).sum + ((resLF 2).map Int.natAbs).sum) (le_refl _) ?_
  · -- groups
    intro f hf G hG
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
    · exact List.all_eq_true.1 grpOK5K_f0 G hG
    · exact List.all_eq_true.1 grpOK5K_f1 G hG
    · exact List.all_eq_true.1 grpOK5K_f2 G hG
  · -- items
    intro f hf
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
    · exact itemsPerm5K_f0
    · exact itemsPerm5K_f1
    · exact itemsPerm5K_f2
  · norm_num [cG, E0, D]
  · norm_num [cO, D]
  · norm_num [cT, D, nuNum, nuDen]
  · norm_num [cE, D, Lden]
  · -- equality kinds
    intro g hg P hP l
    have h := List.all_eq_true.1 eqKinds5K g hg
    have h2 := List.all_eq_true.1 h P hP
    have h3 := List.all_eq_true.1 h2 l (List.mem_finRange l)
    simpa [Bool.or_eq_true, beq_iff_eq] using h3
  · -- slice checks
    intro f hf j
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
    · exact sliceAll0 j
    · exact sliceAll1 j
    · exact sliceAll2 j
  · -- keys of the trees are representatives
    intro f hf e he
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
    · show e.1 ∈ reps0; rw [← t0keys0]; exact List.mem_map_of_mem he
    · show e.1 ∈ reps1; rw [← t0keys1]; exact List.mem_map_of_mem he
    · show e.1 ∈ reps2; rw [← t0keys2]; exact List.mem_map_of_mem he
  · -- offsets
    intro f hf c hc
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
    · exact hoffK0_all c hc
    · exact hoffK1_all c hc
    · exact hoffK2_all c hc
  · -- slack
    decide +kernel

end NPT.K4.D3T497

#print axioms NPT.K4.D3T497.EP_K4_497
