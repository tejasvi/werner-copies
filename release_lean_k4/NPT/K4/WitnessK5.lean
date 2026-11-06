/-
NPT.K4.WitnessK5 — soundness of the five-leg kernel witness check of `NPT.K4.WitnessK5Defs` (the k = 3 version
is `NPT.Cert.Ident.WitnessK`): the source-leg table against `act` (kernel), `witOKK5_sound` (→ `witOK5`), `witGoK5_sound`,
`witGoK5_append`, and `witCheck5_of_slices`: chunk facts on the slices of a decomposition of the class and witness lists
give `witCheck5`.
-/
import NPT.K4.WitnessK5Defs
import NPT.K4.Witness5
import NPT.Cert.Ident.WitnessK

open NPT.Cert.Sem NPT.Brauer NPT.Cert.Ident

namespace NPT.K4

/-- The source leg of `act` (`k = 4`). -/
def srcA5 (σ : Fin 4 → Fin 4) (l : Fin 5) : Fin 5 :=
  if h : l.val < 4 then (((List.finRange 4).find? fun i => σ i = ⟨l.val, h⟩).getD ⟨0, by omega⟩).castSucc else l

lemma srcA5_val : ∀ si, si < 24 → ∀ l : Fin 5, (srcA5 (s4F si) l).val = srcT5 si l.val := by decide +kernel

lemma actK5_eq (g1 g2 : Fin 24) (σ : Fin 4 → Fin 4) (ε : Bool) (w : Fin 5 → Fin 24) (l : Fin 5) :
    act g1 g2 σ ε w l =
      if ε then pinvIdx (mulIdx g1 (mulIdx (w (srcA5 σ l)) g2)) else mulIdx g1 (mulIdx (w (srcA5 σ l)) g2) := rfl

lemma wordAt5_digQ (q : ℕ) (l : Fin 5) : (wordAt5 q l).val = digQ q l.val := by
  show q / 24 ^ l.val % 24 % 24 = q / 24 ^ l.val % 24
  exact Nat.mod_mod _ _

/-! ### Soundness of the per-word check -/

lemma act5_val (g1 g2 : Fin 24) (si : ℕ) (hsi : si < 24) (ε : Bool) (e : ℕ) (he2 : e < 2) (he : ε = true ↔ e = 1)
    (q : ℕ) (l : Fin 5) :
    (act g1 g2 (s4F si) ε (wordAt5 q) l).val = newL5 q g1.val g2.val si e l.val := by
  have hx : (mulIdx g1 (mulIdx (wordAt5 q (srcA5 (s4F si) l)) g2)).val =
      mulT g1.val (mulT (digQ q (srcT5 si l.val)) g2.val) := by
    rw [← srcA5_val si hsi l, ← wordAt5_digQ, mulT_eq, mulT_eq]
  rw [actK5_eq]
  unfold newL5
  by_cases hε : ε = true
  · rw [ite_eq_left hε, he.1 hε, ← hx, (invE_eq _).2]
  · have hne : e ≠ 1 := fun h => hε (he.2 h)
    rw [ite_eq_right hε, show e = 0 by omega, ← hx, (invE_eq _).1]

theorem witOKK5_sound {f q c wc : ℕ} (h : witOKK5 f q c wc = true) : witOK5 f q c wc = true := by
  simp only [witOKK5, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
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
  have hf : f < 3 := gmB_lt h1
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
  simp only [witOK5, Bool.and_eq_true, wordEq5_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [inG_gmB f hf, e1]; exact h1
  · rw [inG_gmB f hf, e2]; exact h2
  · funext l
    apply Fin.ext
    rw [hv l]
    fin_cases l
    · show newL5 q G1 G2 SI E 0 = c / 1 % 24 % 24; omega
    · show newL5 q G1 G2 SI E 1 = c / 24 % 24 % 24; omega
    · show newL5 q G1 G2 SI E 2 = c / 576 % 24 % 24; omega
    · show newL5 q G1 G2 SI E 3 = c / 13824 % 24 % 24; omega
    · show newL5 q G1 G2 SI E 4 = c / 331776 % 24 % 24; omega

/-! ### Lists of words -/

theorem witGoK5_sound (f stop : ℕ) : ∀ (q : ℕ) (cs ws : List ℕ), witGoK5 f stop q cs ws = true →
    witGo5 f q cs ws = true ∧ q + cs.length = stop
  | q, c :: cs, wc :: ws, h => by
    simp only [witGoK5, Bool.and_eq_true] at h
    have ih := witGoK5_sound f stop (q + 1) cs ws h.2
    simp only [witGo5, Bool.and_eq_true, List.length_cons]
    exact ⟨⟨witOKK5_sound h.1, ih.1⟩, by omega⟩
  | q, [], [], h => by
    simp only [witGoK5] at h
    exact ⟨rfl, by simpa using Nat.eq_of_beq_eq_true h⟩
  | _, [], _ :: _, h => by simp [witGoK5] at h
  | _, _ :: _, [], h => by simp [witGoK5] at h

theorem witGoK5_append (f : ℕ) : ∀ (q mid stop : ℕ) (a c b d : List ℕ),
    witGoK5 f mid q a c = true → witGoK5 f stop mid b d = true → witGoK5 f stop q (a ++ b) (c ++ d) = true
  | q, mid, stop, [], [], b, d, h1, h2 => by
    simp only [witGoK5] at h1
    rw [Nat.eq_of_beq_eq_true h1]
    exact h2
  | q, mid, stop, x :: a, y :: c, b, d, h1, h2 => by
    simp only [witGoK5, Bool.and_eq_true] at h1
    simp only [List.cons_append, witGoK5, Bool.and_eq_true]
    exact ⟨h1.1, witGoK5_append f (Nat.succ q) mid stop a c b d h1.2 h2⟩
  | _, _, _, [], _ :: _, _, _, h1, _ => by simp [witGoK5] at h1
  | _, _, _, _ :: _, [], _, _, h1, _ => by simp [witGoK5] at h1

theorem witGoK5_flatten (f N : ℕ) : ∀ (cs ws : List (List ℕ)) (q : ℕ), ws.length = cs.length →
    (∀ k < cs.length, witGoK5 f (q + (k + 1) * N) (q + k * N) (cs.getD k []) (ws.getD k []) = true) →
    witGoK5 f (q + cs.length * N) q cs.flatten ws.flatten = true
  | [], [], q, _, _ => by simp [witGoK5]
  | s :: cs, t :: ws, q, hl, h => by
    simp only [List.flatten_cons, List.length_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.add_zero, List.getD_cons_zero] at h0
    refine witGoK5_append f q (q + N) _ s t _ _ h0 ?_
    have := witGoK5_flatten f N cs ws (q + N) (by simpa using hl) fun k hk => by
      have := h (k + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at this
      rwa [show q + N + (k + 1) * N = q + (k + 1 + 1) * N by ring,
        show q + N + k * N = q + (k + 1) * N by ring]
    rwa [show q + N + cs.length * N = q + (cs.length + 1) * N by ring] at this
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- **Chunked witness check**: if the class and witness lists are the concatenations of slices `cs`, `ws` of `N` words
each (slice `k` = positions `k N .. (k+1) N - 1`) and every slice passes the kernel check, then `witCheck5` holds. -/
theorem witCheck5_of_slices (f N : ℕ) (cls wit : List ℕ) (cs ws : List (List ℕ))
    (hcls : cls = cs.flatten) (hwit : wit = ws.flatten) (hK : cs.length * N = 24 * slen5)
    (hl : ws.length = cs.length)
    (h : ∀ k < cs.length, witGoK5 f ((k + 1) * N) (k * N) (cs.getD k []) (ws.getD k []) = true) :
    witCheck5 f cls wit = true := by
  have hg := witGoK5_flatten f N cs ws 0 hl fun k hk => by
    rw [Nat.zero_add, Nat.zero_add]; exact h k hk
  rw [Nat.zero_add, hK, ← hcls, ← hwit] at hg
  obtain ⟨hgo, hlen⟩ := witGoK5_sound f _ 0 cls wit hg
  rw [Nat.zero_add] at hlen
  unfold witCheck5
  rw [hlen, beq_self_eq_true, Bool.true_and]
  exact hgo

end NPT.K4
