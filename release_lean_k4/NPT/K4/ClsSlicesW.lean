/-
NPT.K4.ClsSlicesW — the class of a K4@497 word read slice by slice: `clsW f w` (the class function of the
witness data) equals `Route.cls5` on the 24 slice lists of family `f`, the form used by the slice checks.
-/
import NPT.K4.ClsLen0
import NPT.K4.ClsLen1
import NPT.K4.ClsLen2
import NPT.K4.Classes.WitAll

open NPT.K4.Classes

namespace NPT.K4.D3T497

theorem clsL_flatten (f : ℕ) (hf : f < 3) : clsL f = (slicesL f).flatten := by
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
  · exact cls0_flatten
  · exact cls1_flatten
  · exact cls2_flatten

theorem slicesL_len (f : ℕ) (hf : f < 3) : ∀ l ∈ slicesL f, l.length = 331776 := by
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
  · exact slices0_len
  · exact slices1_len
  · exact slices2_len

/-- **The class of a word, slice by slice.** -/
theorem clsW_slices (f : ℕ) (hf : f < 3) (w : Fin 5 → Fin 24) :
    clsW f w = Route.cls5 (fun j => (slicesL f).getD j []) w := by
  unfold clsW
  rw [clsL_flatten f hf]
  exact cls_bridge (slicesL f) (slicesL_length f hf) (slicesL_len f hf) w

end NPT.K4.D3T497

#print axioms NPT.K4.D3T497.clsW_slices
