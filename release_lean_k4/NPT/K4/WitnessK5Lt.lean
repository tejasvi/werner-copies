/-
NPT.K4.WitnessK5Lt — the class codes accepted by the five-leg kernel witness check are word positions, `< 24^5`: `witOKK5` compares the code with the position of the acted word exactly. With `witCheck5_of_slices_lt` the
slice facts give, besides `witCheck5`, the bound on every class code (for the code sets of `NPT.K4.IdFactS`).
-/
import NPT.K4.WitnessK5

open NPT.Cert.Sem NPT.Brauer NPT.Cert.Ident

namespace NPT.K4

theorem witOKK5_lt {f q c wc : ℕ} (h : witOKK5 f q c wc = true) : c < 24 * slen5 := by
  simp only [witOKK5, Bool.and_eq_true] at h
  obtain ⟨⟨h1, -⟩, h3⟩ := h
  have hc := Nat.eq_of_beq_eq_true h3
  set G1 := Nat.mod (Nat.div wc 1152) 24 with hG1
  set G2 := Nat.mod (Nat.div wc 48) 24 with hG2
  set SI := Nat.mod (Nat.div wc 2) 24 with hSI
  set E := Nat.mod wc 2 with hE
  have e1 : ((decWit5 wc).1).val = G1 := Nat.mod_mod _ _
  have e2 : ((decWit5 wc).2.1).val = G2 := Nat.mod_mod _ _
  have hsi : SI < 24 := Nat.mod_lt _ (by norm_num)
  have hE2 : E < 2 := Nat.mod_lt _ (by norm_num)
  have hε : (decWit5 wc).2.2.2 = true ↔ E = 1 := beq_iff_eq
  have hv : ∀ l : Fin 5,
      (act (decWit5 wc).1 (decWit5 wc).2.1 (decWit5 wc).2.2.1 (decWit5 wc).2.2.2 (wordAt5 q) l).val =
        newL5 q G1 G2 SI E l.val := by
    intro l
    rw [← e1, ← e2]
    exact act5_val _ _ SI hsi _ E hE2 hε q l
  have hb0 : newL5 q G1 G2 SI E 0 < 24 := (hv 0) ▸ (Fin.isLt _)
  have hb1 : newL5 q G1 G2 SI E 1 < 24 := (hv 1) ▸ (Fin.isLt _)
  have hb2 : newL5 q G1 G2 SI E 2 < 24 := (hv 2) ▸ (Fin.isLt _)
  have hb3 : newL5 q G1 G2 SI E 3 < 24 := (hv 3) ▸ (Fin.isLt _)
  have hb4 : newL5 q G1 G2 SI E 4 < 24 := (hv 4) ▸ (Fin.isLt _)
  have hc' : newL5 q G1 G2 SI E 4 * 331776 + newL5 q G1 G2 SI E 3 * 13824 + newL5 q G1 G2 SI E 2 * 576 +
      newL5 q G1 G2 SI E 1 * 24 + newL5 q G1 G2 SI E 0 = c := hc
  unfold slen5
  omega

/-- Every class code of a checked list of words is a position. -/
theorem witGoK5_lt (f stop : ℕ) : ∀ (q : ℕ) (cs ws : List ℕ), witGoK5 f stop q cs ws = true →
    ∀ c ∈ cs, c < 24 * slen5
  | q, c :: cs, wc :: ws, h, x, hx => by
    simp only [witGoK5, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact witOKK5_lt h.1
    · exact witGoK5_lt f stop (Nat.succ q) cs ws h.2 x hx
  | _, [], _, _, _, hx => absurd hx (List.not_mem_nil)
  | _, _ :: _, [], h, _, _ => by simp [witGoK5] at h

/-- **Chunked witness check with the code bound**: the slice facts give `witCheck5` and `c < 24^5` for every code. -/
theorem witCheck5_of_slices_lt (f N : ℕ) (cls wit : List ℕ) (cs ws : List (List ℕ))
    (hcls : cls = cs.flatten) (hwit : wit = ws.flatten) (hK : cs.length * N = 24 * slen5)
    (hl : ws.length = cs.length)
    (h : ∀ k < cs.length, witGoK5 f ((k + 1) * N) (k * N) (cs.getD k []) (ws.getD k []) = true) :
    witCheck5 f cls wit = true ∧ ∀ c ∈ cls, c < 24 * slen5 := by
  refine ⟨witCheck5_of_slices f N cls wit cs ws hcls hwit hK hl h, ?_⟩
  have hg := witGoK5_flatten f N cs ws 0 hl fun k hk => by
    rw [Nat.zero_add, Nat.zero_add]; exact h k hk
  rw [Nat.zero_add, ← hcls, ← hwit] at hg
  exact witGoK5_lt f _ 0 cls wit hg

/-- The class code of every word is a position (`List.getD` with the default `0`). -/
theorem getD_lt_of_forall (cls : List ℕ) (h : ∀ c ∈ cls, c < 24 * slen5) (i : ℕ) : cls.getD i 0 < 24 * slen5 := by
  rcases Nat.lt_or_ge i cls.length with hi | hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
    unfold slen5; norm_num

end NPT.K4
