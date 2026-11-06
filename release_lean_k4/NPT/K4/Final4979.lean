/-
NPT.K4.Final4979 — **`EP (Fin 4) 3 (4979/10000)`** (five families, native slice checks).

`ep4979_of_slicesB` instantiated with the five-family route data of `NPT.K4.Route.T4979` (rule groups `rgs<f>`, accumulator
trees `t0_<f>` with the offsets `offsLK<f>`, representatives `reps<f>`, residuals `resL<f>`, constants `bP`, `E0`, `cG`,
`cO`, `cT`, `cE`), the data checks (`DataK4979`, kernel), the key lists (`Keys4979`, kernel), the 120 slice checks
`sliceOK<f>_<j>` (native evaluation), the offset sums `hoffK<f>_all` (kernel) and the integer slack check (kernel).
-/
import NPT.K4.EP4979
import NPT.K4.Keys4979
import NPT.K4.DataK4979
import NPT.K4.Route.T4979.HoffK0
import NPT.K4.Route.T4979.Chk0_0
import NPT.K4.Route.T4979.Chk0_1
import NPT.K4.Route.T4979.Chk0_2
import NPT.K4.Route.T4979.Chk0_3
import NPT.K4.Route.T4979.Chk0_4
import NPT.K4.Route.T4979.Chk0_5
import NPT.K4.Route.T4979.Chk0_6
import NPT.K4.Route.T4979.Chk0_7
import NPT.K4.Route.T4979.Chk0_8
import NPT.K4.Route.T4979.Chk0_9
import NPT.K4.Route.T4979.Chk0_10
import NPT.K4.Route.T4979.Chk0_11
import NPT.K4.Route.T4979.Chk0_12
import NPT.K4.Route.T4979.Chk0_13
import NPT.K4.Route.T4979.Chk0_14
import NPT.K4.Route.T4979.Chk0_15
import NPT.K4.Route.T4979.Chk0_16
import NPT.K4.Route.T4979.Chk0_17
import NPT.K4.Route.T4979.Chk0_18
import NPT.K4.Route.T4979.Chk0_19
import NPT.K4.Route.T4979.Chk0_20
import NPT.K4.Route.T4979.Chk0_21
import NPT.K4.Route.T4979.Chk0_22
import NPT.K4.Route.T4979.Chk0_23
import NPT.K4.Route.T4979.HoffK1
import NPT.K4.Route.T4979.Chk1_0
import NPT.K4.Route.T4979.Chk1_1
import NPT.K4.Route.T4979.Chk1_2
import NPT.K4.Route.T4979.Chk1_3
import NPT.K4.Route.T4979.Chk1_4
import NPT.K4.Route.T4979.Chk1_5
import NPT.K4.Route.T4979.Chk1_6
import NPT.K4.Route.T4979.Chk1_7
import NPT.K4.Route.T4979.Chk1_8
import NPT.K4.Route.T4979.Chk1_9
import NPT.K4.Route.T4979.Chk1_10
import NPT.K4.Route.T4979.Chk1_11
import NPT.K4.Route.T4979.Chk1_12
import NPT.K4.Route.T4979.Chk1_13
import NPT.K4.Route.T4979.Chk1_14
import NPT.K4.Route.T4979.Chk1_15
import NPT.K4.Route.T4979.Chk1_16
import NPT.K4.Route.T4979.Chk1_17
import NPT.K4.Route.T4979.Chk1_18
import NPT.K4.Route.T4979.Chk1_19
import NPT.K4.Route.T4979.Chk1_20
import NPT.K4.Route.T4979.Chk1_21
import NPT.K4.Route.T4979.Chk1_22
import NPT.K4.Route.T4979.Chk1_23
import NPT.K4.Route.T4979.HoffK2
import NPT.K4.Route.T4979.Chk2_0
import NPT.K4.Route.T4979.Chk2_1
import NPT.K4.Route.T4979.Chk2_2
import NPT.K4.Route.T4979.Chk2_3
import NPT.K4.Route.T4979.Chk2_4
import NPT.K4.Route.T4979.Chk2_5
import NPT.K4.Route.T4979.Chk2_6
import NPT.K4.Route.T4979.Chk2_7
import NPT.K4.Route.T4979.Chk2_8
import NPT.K4.Route.T4979.Chk2_9
import NPT.K4.Route.T4979.Chk2_10
import NPT.K4.Route.T4979.Chk2_11
import NPT.K4.Route.T4979.Chk2_12
import NPT.K4.Route.T4979.Chk2_13
import NPT.K4.Route.T4979.Chk2_14
import NPT.K4.Route.T4979.Chk2_15
import NPT.K4.Route.T4979.Chk2_16
import NPT.K4.Route.T4979.Chk2_17
import NPT.K4.Route.T4979.Chk2_18
import NPT.K4.Route.T4979.Chk2_19
import NPT.K4.Route.T4979.Chk2_20
import NPT.K4.Route.T4979.Chk2_21
import NPT.K4.Route.T4979.Chk2_22
import NPT.K4.Route.T4979.Chk2_23
import NPT.K4.Route.T4979.HoffK3
import NPT.K4.Route.T4979.Chk3_0
import NPT.K4.Route.T4979.Chk3_1
import NPT.K4.Route.T4979.Chk3_2
import NPT.K4.Route.T4979.Chk3_3
import NPT.K4.Route.T4979.Chk3_4
import NPT.K4.Route.T4979.Chk3_5
import NPT.K4.Route.T4979.Chk3_6
import NPT.K4.Route.T4979.Chk3_7
import NPT.K4.Route.T4979.Chk3_8
import NPT.K4.Route.T4979.Chk3_9
import NPT.K4.Route.T4979.Chk3_10
import NPT.K4.Route.T4979.Chk3_11
import NPT.K4.Route.T4979.Chk3_12
import NPT.K4.Route.T4979.Chk3_13
import NPT.K4.Route.T4979.Chk3_14
import NPT.K4.Route.T4979.Chk3_15
import NPT.K4.Route.T4979.Chk3_16
import NPT.K4.Route.T4979.Chk3_17
import NPT.K4.Route.T4979.Chk3_18
import NPT.K4.Route.T4979.Chk3_19
import NPT.K4.Route.T4979.Chk3_20
import NPT.K4.Route.T4979.Chk3_21
import NPT.K4.Route.T4979.Chk3_22
import NPT.K4.Route.T4979.Chk3_23
import NPT.K4.Route.T4979.HoffK4
import NPT.K4.Route.T4979.Chk4_0
import NPT.K4.Route.T4979.Chk4_1
import NPT.K4.Route.T4979.Chk4_2
import NPT.K4.Route.T4979.Chk4_3
import NPT.K4.Route.T4979.Chk4_4
import NPT.K4.Route.T4979.Chk4_5
import NPT.K4.Route.T4979.Chk4_6
import NPT.K4.Route.T4979.Chk4_7
import NPT.K4.Route.T4979.Chk4_8
import NPT.K4.Route.T4979.Chk4_9
import NPT.K4.Route.T4979.Chk4_10
import NPT.K4.Route.T4979.Chk4_11
import NPT.K4.Route.T4979.Chk4_12
import NPT.K4.Route.T4979.Chk4_13
import NPT.K4.Route.T4979.Chk4_14
import NPT.K4.Route.T4979.Chk4_15
import NPT.K4.Route.T4979.Chk4_16
import NPT.K4.Route.T4979.Chk4_17
import NPT.K4.Route.T4979.Chk4_18
import NPT.K4.Route.T4979.Chk4_19
import NPT.K4.Route.T4979.Chk4_20
import NPT.K4.Route.T4979.Chk4_21
import NPT.K4.Route.T4979.Chk4_22
import NPT.K4.Route.T4979.Chk4_23

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.K4 NPT.K4.Route.T4979

namespace NPT.K4.D3T4979

theorem sliceAll0 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 10000 4979 cG cO cT cE 0 rgs0 j)
    ((slicesL5 0).getD j.val []) (Route.tOff t0_0 (offsLK0.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK0_0, sliceOK0_1, sliceOK0_2, sliceOK0_3, sliceOK0_4, sliceOK0_5, sliceOK0_6, sliceOK0_7, sliceOK0_8, sliceOK0_9, sliceOK0_10, sliceOK0_11, sliceOK0_12, sliceOK0_13, sliceOK0_14, sliceOK0_15, sliceOK0_16, sliceOK0_17, sliceOK0_18, sliceOK0_19, sliceOK0_20, sliceOK0_21, sliceOK0_22, sliceOK0_23]

theorem sliceAll1 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 10000 4979 cG cO cT cE 1 rgs1 j)
    ((slicesL5 1).getD j.val []) (Route.tOff t0_1 (offsLK1.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK1_0, sliceOK1_1, sliceOK1_2, sliceOK1_3, sliceOK1_4, sliceOK1_5, sliceOK1_6, sliceOK1_7, sliceOK1_8, sliceOK1_9, sliceOK1_10, sliceOK1_11, sliceOK1_12, sliceOK1_13, sliceOK1_14, sliceOK1_15, sliceOK1_16, sliceOK1_17, sliceOK1_18, sliceOK1_19, sliceOK1_20, sliceOK1_21, sliceOK1_22, sliceOK1_23]

theorem sliceAll2 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 10000 4979 cG cO cT cE 2 rgs2 j)
    ((slicesL5 2).getD j.val []) (Route.tOff t0_2 (offsLK2.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK2_0, sliceOK2_1, sliceOK2_2, sliceOK2_3, sliceOK2_4, sliceOK2_5, sliceOK2_6, sliceOK2_7, sliceOK2_8, sliceOK2_9, sliceOK2_10, sliceOK2_11, sliceOK2_12, sliceOK2_13, sliceOK2_14, sliceOK2_15, sliceOK2_16, sliceOK2_17, sliceOK2_18, sliceOK2_19, sliceOK2_20, sliceOK2_21, sliceOK2_22, sliceOK2_23]

theorem sliceAll3 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 10000 4979 cG cO cT cE 3 rgs3 j)
    ((slicesL5 3).getD j.val []) (Route.tOff t0_3 (offsLK3.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK3_0, sliceOK3_1, sliceOK3_2, sliceOK3_3, sliceOK3_4, sliceOK3_5, sliceOK3_6, sliceOK3_7, sliceOK3_8, sliceOK3_9, sliceOK3_10, sliceOK3_11, sliceOK3_12, sliceOK3_13, sliceOK3_14, sliceOK3_15, sliceOK3_16, sliceOK3_17, sliceOK3_18, sliceOK3_19, sliceOK3_20, sliceOK3_21, sliceOK3_22, sliceOK3_23]

theorem sliceAll4 : ∀ j : Fin 24, Route.sliceCheck bP (Route.parts5B cert 10000 4979 cG cO cT cE 4 rgs4 j)
    ((slicesL5 4).getD j.val []) (Route.tOff t0_4 (offsLK4.getD j.val [])) = true := by
  intro j
  fin_cases j
  exacts [sliceOK4_0, sliceOK4_1, sliceOK4_2, sliceOK4_3, sliceOK4_4, sliceOK4_5, sliceOK4_6, sliceOK4_7, sliceOK4_8, sliceOK4_9, sliceOK4_10, sliceOK4_11, sliceOK4_12, sliceOK4_13, sliceOK4_14, sliceOK4_15, sliceOK4_16, sliceOK4_17, sliceOK4_18, sliceOK4_19, sliceOK4_20, sliceOK4_21, sliceOK4_22, sliceOK4_23]

/-- The residual lists by family (a constant, so the mass bound below is syntactic). -/
def resLF (f : ℕ) : List ℤ :=
  if f = 0 then resL0 else if f = 1 then resL1 else if f = 2 then resL2 else if f = 3 then resL3 else resL4

/-- **The endpoint property of the K4 qutrit problem at t = 4979/10000** (all five families). -/
theorem EP_K4_4979 : NPT.EP (Fin 4) 3 (4979 / 10000) := by
  refine ep4979_of_slicesB
    (fun f => if f = 0 then rgs0 else if f = 1 then rgs1 else if f = 2 then rgs2 else if f = 3 then rgs3 else rgs4)
    (fun f => if f = 0 then t0_0 else if f = 1 then t0_1 else if f = 2 then t0_2 else if f = 3 then t0_3 else t0_4)
    (fun f j => (if f = 0 then offsLK0 else if f = 1 then offsLK1 else if f = 2 then offsLK2 else if f = 3 then offsLK3
      else offsLK4).getD j [])
    bP E0 cG cO cT cE ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (fun f => if f = 0 then reps0 else if f = 1 then reps1 else if f = 2 then reps2 else if f = 3 then reps3 else reps4)
    resLF ?_ ?_
    (((resLF 0).map Int.natAbs).sum + ((resLF 1).map Int.natAbs).sum + ((resLF 2).map Int.natAbs).sum +
      ((resLF 3).map Int.natAbs).sum + ((resLF 4).map Int.natAbs).sum) (le_refl _) ?_
  · -- groups
    intro f hf G hG
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) with rfl | rfl | rfl | rfl | rfl
    · exact List.all_eq_true.1 grpOK5K_f0 G hG
    · exact List.all_eq_true.1 grpOK5K_f1 G hG
    · exact List.all_eq_true.1 grpOK5K_f2 G hG
    · exact List.all_eq_true.1 grpOK5K_f3 G hG
    · exact List.all_eq_true.1 grpOK5K_f4 G hG
  · -- items
    intro f hf
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) with rfl | rfl | rfl | rfl | rfl
    · exact itemsPerm5K_f0
    · exact itemsPerm5K_f1
    · exact itemsPerm5K_f2
    · exact itemsPerm5K_f3
    · exact itemsPerm5K_f4
  · norm_num [cG, E0, D5]
  · norm_num [cO, D5]
  · norm_num [cT, D5, nuNum, nuDen]
  · norm_num [cE, D5, Lden]
  · -- equality kinds
    intro g hg P hP l
    have h := List.all_eq_true.1 eqKinds5K g hg
    have h2 := List.all_eq_true.1 h P hP
    have h3 := List.all_eq_true.1 h2 l (List.mem_finRange l)
    simpa [Bool.or_eq_true, beq_iff_eq] using h3
  · -- slice checks
    intro f hf j
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) with rfl | rfl | rfl | rfl | rfl
    · exact sliceAll0 j
    · exact sliceAll1 j
    · exact sliceAll2 j
    · exact sliceAll3 j
    · exact sliceAll4 j
  · -- keys of the trees are representatives
    intro f hf e he
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) with rfl | rfl | rfl | rfl | rfl
    · show e.1 ∈ reps0; rw [← t0keys0]; exact List.mem_map_of_mem he
    · show e.1 ∈ reps1; rw [← t0keys1]; exact List.mem_map_of_mem he
    · show e.1 ∈ reps2; rw [← t0keys2]; exact List.mem_map_of_mem he
    · show e.1 ∈ reps3; rw [← t0keys3]; exact List.mem_map_of_mem he
    · show e.1 ∈ reps4; rw [← t0keys4]; exact List.mem_map_of_mem he
  · -- offsets
    intro f hf c hc
    rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 ∨ f = 4) with rfl | rfl | rfl | rfl | rfl
    · exact hoffK0_all c hc
    · exact hoffK1_all c hc
    · exact hoffK2_all c hc
    · exact hoffK3_all c hc
    · exact hoffK4_all c hc
  · -- slack
    decide +kernel

end NPT.K4.D3T4979

#print axioms NPT.K4.D3T4979.EP_K4_4979
