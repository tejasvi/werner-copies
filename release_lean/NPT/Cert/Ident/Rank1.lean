/-
NPT.Cert.Ident.Rank1 — rank-one parts `c · E0(w0) E1(w1) E2(w2) E3(w3)` (objective, equality entries).
-/
import NPT.Cert.Ident.Paths
import NPT.Cert.Ident.Family

open BigOperators Finset

namespace NPT.Cert.Ident

/-- Spec of a rank-one part: leg `l` has the single column `E l`, the leaf is the scalar `c`. -/
def rank1Spec (E : ℕ → Fin 24 → ℤ) (c : ℤ) : Spec where
  rows l := (List.finRange 24).map fun p => [SInt.ofInt (E l p)]
  dimsq _ := 1
  leaf _ _ _ _ := [SInt.ofInt c]

/-- The single-path tree of a rank-one part. -/
def rank1Tree : List Nd3 := [⟨3, [⟨2, [⟨1, [⟨0, []⟩]⟩]⟩]⟩]

def rank1Part (E : ℕ → Fin 24 → ℤ) (c : ℤ) : Part := ⟨rank1Spec E c, rank1Tree⟩

lemma rank1Spec_rows (E : ℕ → Fin 24 → ℤ) (c : ℤ) : ∀ m, ((rank1Spec E c).rows m).length = 24 := by
  intro m; simp [rank1Spec]

lemma map_finRange_getD {β : Type} (f : Fin 24 → β) (d : β) (p : Fin 24) :
    ((List.finRange 24).map f).getD p.val d = f p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simp)]
  simp

lemma rank1_aval (E : ℕ → Fin 24 → ℤ) (c : ℤ) (l : ℕ) (p : Fin 24) :
    aval ((rank1Spec E c).rows l) p.val 0 = E l p := by
  simp only [rank1Spec, aval]
  rw [map_finRange_getD]
  simp [SInt.val_ofInt]

lemma rank1_spec (E : ℕ → Fin 24 → ℤ) (c : ℤ) (w0 w1 w2 w3 : Fin 24) :
    specTree (rank1Spec E c) rank1Tree w0.val w1.val w2.val w3.val = c * (E 0 w0 * E 1 w1 * E 2 w2 * E 3 w3) := by
  rw [specTree_paths]
  simp only [rank1Tree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, boxF]
  simp only [show (rank1Spec E c).dimsq = fun _ => 1 from rfl, Finset.sum_range_one, rank1_aval]
  simp only [rank1Spec, gv, zero_mul, zero_add, List.getD_cons_zero, SInt.val_ofInt]
  ring

end NPT.Cert.Ident
