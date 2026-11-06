/-
NPT.K4.ClsSlices3 — the five-family class list of families 40 and 04 (one shared S_4 data set) as 24 slices (auxiliary
letter): `cls3 = slices3.flatten`; the slice lengths are in `ClsLen3`.
-/
import NPT.K4.ClsBridge
import NPT.K4.Classes.Class3

open NPT.K4.Classes

namespace NPT.K4.D3T4979

def slices3 : List (List ℕ) := [cls3_0, cls3_1, cls3_2, cls3_3, cls3_4, cls3_5, cls3_6, cls3_7, cls3_8, cls3_9, cls3_10, cls3_11, cls3_12, cls3_13, cls3_14, cls3_15, cls3_16, cls3_17, cls3_18, cls3_19, cls3_20, cls3_21, cls3_22, cls3_23]

theorem cls3_flatten : cls3 = slices3.flatten := by
  simp only [cls3, slices3, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem slices3_length : slices3.length = 24 := rfl

end NPT.K4.D3T4979
