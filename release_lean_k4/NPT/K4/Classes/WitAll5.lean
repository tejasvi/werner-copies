/-
NPT.K4.Classes.WitAll5 — the orbit-witness fields for the five families: `f = 0, 1, 2` ('31', '22', '13')
from `NPT.K4.Classes.WitAll`, `f = 3, 4` ('40', '04', group S4) from the shared S4 data `cls3`, `wit3` checked by
`witCheckS_f3`.  Fields in the form of `NPT.K4.IdFactS5` (`inG5` of `NPT.K4.Phys5`; all of S4 for `f = 3, 4`).
-/
import NPT.K4.Classes.WitAll
import NPT.K4.Classes.WitK3
import NPT.K4.Phys5

open NPT.Cert.Sem NPT.K4

namespace NPT.K4.Classes

lemma inG5_S4 : ∀ g : Fin 24, inG5 3 g = true ∧ inG5 4 g = true := by decide

/-- Class codes by family (`f = 3, 4` share the S4 data). -/
def clsL5 (f : ℕ) : List ℕ := if f < 3 then clsL f else cls3
/-- Witness codes by family. -/
def witL5 (f : ℕ) : List ℕ := if f < 3 then witL f else wit3

/-- The class of a word. -/
def clsW5 (f : ℕ) (w : Fin 5 → Fin 24) : ℕ := (clsL5 f).getD (posW5 w) 0
/-- The representative of a class code. -/
def repW5 (_f c : ℕ) : Fin 5 → Fin 24 := wordAt5 c
/-- The witness of a word. -/
def witW5 (f : ℕ) (w : Fin 5 → Fin 24) : Fin 24 × Fin 24 × (Fin 4 → Fin 4) × Bool :=
  decWit5 ((witL5 f).getD (posW5 w) 0)

lemma witW5_lt {f : ℕ} (h : f < 3) (w : Fin 5 → Fin 24) : witW5 f w = witW f w := by
  simp only [witW5, witW, witL5, if_pos h]

lemma clsW5_lt {f : ℕ} (h : f < 3) (w : Fin 5 → Fin 24) : clsW5 f w = clsW f w := by
  simp only [clsW5, clsW, clsL5, if_pos h]

lemma witW5_ge {f : ℕ} (h : ¬ f < 3) (w : Fin 5 → Fin 24) : witW5 f w = decWit5 (wit3.getD (posW5 w) 0) := by
  simp only [witW5, witL5, if_neg h]

lemma clsW5_ge {f : ℕ} (h : ¬ f < 3) (w : Fin 5 → Fin 24) : clsW5 f w = cls3.getD (posW5 w) 0 := by
  simp only [clsW5, clsL5, if_neg h]

theorem hG5' : ∀ f < 5, ∀ w, inG5 f (witW5 f w).1 = true ∧ inG5 f (witW5 f w).2.1 = true := by
  intro f hf w
  by_cases h3 : f < 3
  · rw [witW5_lt h3, inG5_lt3 h3]
    exact hG5 f h3 w
  · rcases (by omega : f = 3 ∨ f = 4) with rfl | rfl
    · exact ⟨(inG5_S4 _).1, (inG5_S4 _).1⟩
    · exact ⟨(inG5_S4 _).2, (inG5_S4 _).2⟩

theorem hσ5' : ∀ f < 5, ∀ w, Function.Bijective (witW5 f w).2.2.1 := fun _ _ _ => decWit5_bij _

/-- Every class code is a word position (`codes f = Finset.range (24 * slen5)` contains it). -/
theorem hcodes5' : ∀ f < 5, ∀ w, clsW5 f w ∈ Finset.range (24 * slen5) := by
  intro f _ w
  by_cases h3 : f < 3
  · rw [clsW5_lt h3]; exact hcodes5 f h3 w
  · rw [clsW5_ge h3]; exact Finset.mem_range.2 (getD_lt_of_forall _ cls3_lt _)

theorem hrep5' : ∀ f < 5, ∀ w,
    act (witW5 f w).1 (witW5 f w).2.1 (witW5 f w).2.2.1 (witW5 f w).2.2.2 w = repW5 f (clsW5 f w) := by
  intro f _ w
  by_cases h3 : f < 3
  · rw [witW5_lt h3, clsW5_lt h3]; exact hrep5 f h3 w
  · rw [witW5_ge h3, clsW5_ge h3]; exact witCheckS_fields cls3 wit3 witCheckS_f3 w

end NPT.K4.Classes
