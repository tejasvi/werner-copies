/-
NPT.K4.ClsBridge — reading a per-family class list (word positions `posW5`, auxiliary letter slowest) slice by slice.  The class data of a family is the concatenation of 24 slice lists of `24^4 = 331776` entries; the class
of a word is then the entry at `posW (Fin.init w)` of the slice selected by its auxiliary letter (`Route.cls5`).
`cls_bridge` gives this for any list of 24 blocks of length 331776.
-/
import NPT.K4.Route.HsumS
import NPT.K4.Witness5

open NPT.Cert.Ident

namespace NPT.K4

/-- Reading a concatenation of equal-length blocks. -/
lemma getD_flatten_block (S : ℕ) : ∀ (Ls : List (List ℕ)), (∀ l ∈ Ls, l.length = S) →
    ∀ j q : ℕ, j < Ls.length → q < S → Ls.flatten.getD (j * S + q) 0 = (Ls.getD j []).getD q 0
  | [], _, j, _, hj, _ => absurd hj (by simp)
  | l :: Ls, hlen, j, q, hj, hq => by
    have hl : l.length = S := hlen l (by simp)
    rw [List.flatten_cons]
    rcases j with _ | j
    · rw [zero_mul, zero_add, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      rfl
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hl]; nlinarith),
        ← List.getD_eq_getElem?_getD]
      have e : (j + 1) * S + q - l.length = j * S + q := by rw [hl]; ring_nf; omega
      rw [e]
      exact getD_flatten_block S Ls (fun l' hl' => hlen l' (by simp [hl'])) j q
        (by simpa using hj) hq

lemma posW_init_lt (w : Fin 5 → Fin 24) : posW (Fin.init w) < 331776 := by
  unfold posW
  have h0 := (w 0).isLt; have h1 := (w 1).isLt; have h2 := (w 2).isLt; have h3 := (w 3).isLt
  simp only [Fin.init]
  have e0 : (Fin.castSucc (0 : Fin 4) : Fin 5) = 0 := rfl
  have e1 : (Fin.castSucc (1 : Fin 4) : Fin 5) = 1 := rfl
  have e2 : (Fin.castSucc (2 : Fin 4) : Fin 5) = 2 := rfl
  have e3 : (Fin.castSucc (3 : Fin 4) : Fin 5) = 3 := rfl
  rw [e0, e1, e2, e3]
  omega

lemma posW5_split (w : Fin 5 → Fin 24) : posW5 w = (w 4).val * 331776 + posW (Fin.init w) := by
  unfold posW5 posW
  simp only [Fin.init]
  have e0 : (Fin.castSucc (0 : Fin 4) : Fin 5) = 0 := rfl
  have e1 : (Fin.castSucc (1 : Fin 4) : Fin 5) = 1 := rfl
  have e2 : (Fin.castSucc (2 : Fin 4) : Fin 5) = 2 := rfl
  have e3 : (Fin.castSucc (3 : Fin 4) : Fin 5) = 3 := rfl
  rw [e0, e1, e2, e3]
  ring

/-- **Class of a word, slice by slice.** -/
theorem cls_bridge (Ls : List (List ℕ)) (hn : Ls.length = 24) (hlen : ∀ l ∈ Ls, l.length = 331776)
    (w : Fin 5 → Fin 24) : Ls.flatten.getD (posW5 w) 0 = Route.cls5 (fun j => Ls.getD j []) w := by
  rw [posW5_split, getD_flatten_block 331776 Ls hlen (w 4).val (posW (Fin.init w)) (by rw [hn]; exact (w 4).isLt)
    (posW_init_lt w)]
  rfl

end NPT.K4

#print axioms NPT.K4.cls_bridge
