/-
NPT.K4.Classes.WitAll — the orbit-witness fields of the K4 identity fact (k = 4, words `Fin 5 → Fin 24`) for the three
families, from the kernel witness checks `witCheck5_f0/f1/f2`: class codes `clsL f`, witness codes `witL f`,
and the fields `hG`, `hσ`, `hrep` of `Sem.IdFact` in the form `cls f w = (clsL f).getD (posW5 w) 0`,
`rep f c = wordAt5 c`, `wit f w = decWit5 ((witL f).getD (posW5 w) 0)`.
-/
import NPT.K4.Classes.WitK0
import NPT.K4.Classes.WitK1
import NPT.K4.Classes.WitK2
import NPT.K4.WitnessK5Lt

open NPT.Cert.Sem NPT.K4

namespace NPT.K4.Classes

/-- Class codes by family (`f = 0, 1, 2` = '31', '22', '13'). -/
def clsL (f : ℕ) : List ℕ := if f = 0 then cls0 else if f = 1 then cls1 else cls2
/-- Witness codes by family. -/
def witL (f : ℕ) : List ℕ := if f = 0 then wit0 else if f = 1 then wit1 else wit2

theorem witCheck5_all (f : ℕ) (hf : f < 3) : witCheck5 f (clsL f) (witL f) = true := by
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
  · exact witCheck5_f0
  · exact witCheck5_f1
  · exact witCheck5_f2

/-- The class of a word. -/
def clsW (f : ℕ) (w : Fin 5 → Fin 24) : ℕ := (clsL f).getD (posW5 w) 0
/-- The representative of a class code. -/
def repW (_f c : ℕ) : Fin 5 → Fin 24 := wordAt5 c
/-- The witness of a word. -/
def witW (f : ℕ) (w : Fin 5 → Fin 24) : Fin 24 × Fin 24 × (Fin 4 → Fin 4) × Bool := decWit5 ((witL f).getD (posW5 w) 0)

theorem hG5 : ∀ f < 3, ∀ w, inG f (witW f w).1 = true ∧ inG f (witW f w).2.1 = true := fun f hf w =>
  ⟨(witCheck5_fields f _ _ (witCheck5_all f hf) w).1, (witCheck5_fields f _ _ (witCheck5_all f hf) w).2.1⟩

theorem hσ5 : ∀ f < 3, ∀ w, Function.Bijective (witW f w).2.2.1 := fun f _ w => decWit5_bij _

theorem clsL_lt (f : ℕ) (hf : f < 3) : ∀ c ∈ clsL f, c < 24 * slen5 := by
  rcases (by omega : f = 0 ∨ f = 1 ∨ f = 2) with rfl | rfl | rfl
  · exact cls0_lt
  · exact cls1_lt
  · exact cls2_lt

/-- Every class code is a word position (`codes f = Finset.range (24 * slen5)` contains it). -/
theorem hcodes5 : ∀ f < 3, ∀ w, clsW f w ∈ Finset.range (24 * slen5) := fun f hf w =>
  Finset.mem_range.2 (getD_lt_of_forall _ (clsL_lt f hf) _)

theorem hrep5 : ∀ f < 3, ∀ w,
    act (witW f w).1 (witW f w).2.1 (witW f w).2.2.1 (witW f w).2.2.2 w = repW f (clsW f w) := fun f hf w =>
  (witCheck5_fields f _ _ (witCheck5_all f hf) w).2.2

end NPT.K4.Classes
