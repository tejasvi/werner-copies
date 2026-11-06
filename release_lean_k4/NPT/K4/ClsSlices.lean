/-
NPT.K4.ClsSlices — the K4@497 class lists as 24 slices (auxiliary letter): `cls<f> = slices<f>.flatten`.
The slice lengths are checked in `ClsLen0/1/2` (one family per module, for memory); the class of a word is then read
slice by slice with `cls_bridge`.  The slice checks of the route use `fun j => (slicesL f).getD j []` as their
per-slice class lists.
-/
import NPT.K4.ClsBridge
import NPT.K4.Classes.Class0
import NPT.K4.Classes.Class1
import NPT.K4.Classes.Class2

open NPT.K4.Classes

namespace NPT.K4.D3T497

def slices0 : List (List ℕ) := [cls0_0, cls0_1, cls0_2, cls0_3, cls0_4, cls0_5, cls0_6, cls0_7, cls0_8, cls0_9, cls0_10, cls0_11, cls0_12, cls0_13, cls0_14, cls0_15, cls0_16, cls0_17, cls0_18, cls0_19, cls0_20, cls0_21, cls0_22, cls0_23]
def slices1 : List (List ℕ) := [cls1_0, cls1_1, cls1_2, cls1_3, cls1_4, cls1_5, cls1_6, cls1_7, cls1_8, cls1_9, cls1_10, cls1_11, cls1_12, cls1_13, cls1_14, cls1_15, cls1_16, cls1_17, cls1_18, cls1_19, cls1_20, cls1_21, cls1_22, cls1_23]
def slices2 : List (List ℕ) := [cls2_0, cls2_1, cls2_2, cls2_3, cls2_4, cls2_5, cls2_6, cls2_7, cls2_8, cls2_9, cls2_10, cls2_11, cls2_12, cls2_13, cls2_14, cls2_15, cls2_16, cls2_17, cls2_18, cls2_19, cls2_20, cls2_21, cls2_22, cls2_23]

/-- The 24 slice lists of family `f` (`f < 3`). -/
def slicesL (f : ℕ) : List (List ℕ) := if f = 0 then slices0 else if f = 1 then slices1 else slices2

theorem cls0_flatten : cls0 = slices0.flatten := by
  simp only [cls0, slices0, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
theorem cls1_flatten : cls1 = slices1.flatten := by
  simp only [cls1, slices1, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
theorem cls2_flatten : cls2 = slices2.flatten := by
  simp only [cls2, slices2, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem slicesL_length (f : ℕ) (hf : f < 3) : (slicesL f).length = 24 := by
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl <;> rfl

end NPT.K4.D3T497
