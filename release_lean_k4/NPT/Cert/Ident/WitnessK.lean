/-
NPT.Cert.Ident.WitnessK — soundness of the kernel witness check of `WitnessKDefs`: the packed tables
against `mulIdx`, `pinvIdx`, the source factor of `act` and `inG` (kernel); `witOKK_sound` (→ `witOK`);
`witGoK_sound`, `witGoK_append`, `stripsR_sound`; and `witCheck_of_slices`: chunk facts on the slices of a
decomposition of the class and witness lists give `witCheck`.
-/
import NPT.Cert.Ident.WitnessKDefs
import NPT.Cert.Ident.Witness

open NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-! ### The tables (kernel) -/

lemma mulT_eq : ∀ p q : Fin 24, mulT p.val q.val = (mulIdx p q).val := by decide +kernel

lemma invE_eq : ∀ x : Fin 24, invE 0 x.val = x.val ∧ invE 1 x.val = (pinvIdx x).val := by decide +kernel

/-- The source factor of `act` (`k = 3`). -/
def srcA (σ : Fin 3 → Fin 3) (l : Fin 4) : Fin 4 :=
  if h : l.val < 3 then (((List.finRange 3).find? fun i => σ i = ⟨l.val, h⟩).getD ⟨0, by omega⟩).castSucc else l

lemma srcA_val : ∀ si, si < 6 → ∀ l : Fin 4, (srcA (s3F si) l).val = srcT si l.val := by decide +kernel

lemma inG_gmB : ∀ f, f < 3 → ∀ g : Fin 24, inG f g = gmB f g.val := by decide +kernel

lemma gmB_lt {f g : ℕ} (h : gmB f g = true) : f < 3 := by
  by_contra hf
  have hz : Nat.shiftRight GT (Nat.add (Nat.mul 24 f) g) = 0 := by
    show GT >>> (24 * f + g) = 0
    rw [Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt
    calc GT < 2 ^ 72 := by decide
      _ ≤ 2 ^ (24 * f + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [gmB, hz] at h
  exact absurd h (by decide)

lemma actK_eq (g1 g2 : Fin 24) (σ : Fin 3 → Fin 3) (ε : Bool) (w : Fin 4 → Fin 24) (l : Fin 4) :
    act g1 g2 σ ε w l =
      if ε then pinvIdx (mulIdx g1 (mulIdx (w (srcA σ l)) g2)) else mulIdx g1 (mulIdx (w (srcA σ l)) g2) := rfl

lemma wordAt_digQ (q : ℕ) (l : Fin 4) : (wordAt q l).val = digQ q l.val := by
  fin_cases l
  · show q % 24 % 24 = q / 1 % 24; rw [Nat.div_one, Nat.mod_mod]
  · show q / 24 % 24 % 24 = q / 24 % 24; exact Nat.mod_mod _ _
  · show q / 576 % 24 % 24 = q / 576 % 24; exact Nat.mod_mod _ _
  · show q / 13824 % 24 = q / 13824 % 24; rfl

/-! ### Soundness of the per-word check -/

lemma act_val (g1 g2 : Fin 24) (si : ℕ) (hsi : si < 6) (ε : Bool) (e : ℕ) (he2 : e < 2) (he : ε = true ↔ e = 1)
    (q : ℕ) (l : Fin 4) :
    (act g1 g2 (s3F si) ε (wordAt q) l).val = newL q g1.val g2.val si e l.val := by
  have hx : (mulIdx g1 (mulIdx (wordAt q (srcA (s3F si) l)) g2)).val =
      mulT g1.val (mulT (digQ q (srcT si l.val)) g2.val) := by
    rw [← srcA_val si hsi l, ← wordAt_digQ, mulT_eq, mulT_eq]
  rw [actK_eq]
  unfold newL
  by_cases hε : ε = true
  · rw [ite_eq_left hε, he.1 hε, ← hx, (invE_eq _).2]
  · have hne : e ≠ 1 := fun h => hε (he.2 h)
    rw [ite_eq_right hε, show e = 0 by omega, ← hx, (invE_eq _).1]

theorem witOKK_sound {f q c wc : ℕ} (h : witOKK f q c wc = true) : witOK f q c wc = true := by
  simp only [witOKK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hc := Nat.eq_of_beq_eq_true h3
  set G1 := Nat.mod (Nat.div wc 288) 24 with hG1
  set G2 := Nat.mod (Nat.div wc 12) 24 with hG2
  set SI := Nat.mod (Nat.div wc 2) 6 with hSI
  set E := Nat.mod wc 2 with hE
  have e1 : ((decWit wc).1).val = G1 := Nat.mod_mod _ _
  have e2 : ((decWit wc).2.1).val = G2 := Nat.mod_mod _ _
  have hsi : SI < 6 := Nat.mod_lt _ (by norm_num)
  have hE2 : E < 2 := Nat.mod_lt _ (by norm_num)
  have hε : (decWit wc).2.2.2 = true ↔ E = 1 := beq_iff_eq
  have hf : f < 3 := gmB_lt h1
  have hv : ∀ l : Fin 4,
      (act (decWit wc).1 (decWit wc).2.1 (decWit wc).2.2.1 (decWit wc).2.2.2 (wordAt q) l).val =
        newL q G1 G2 SI E l.val := by
    intro l
    rw [← e1, ← e2]
    exact act_val _ _ SI hsi _ E hE2 hε q l
  have hb0 : newL q G1 G2 SI E 0 < 24 := (hv 0) ▸ (Fin.isLt _)
  have hb1 : newL q G1 G2 SI E 1 < 24 := (hv 1) ▸ (Fin.isLt _)
  have hb2 : newL q G1 G2 SI E 2 < 24 := (hv 2) ▸ (Fin.isLt _)
  have hb3 : newL q G1 G2 SI E 3 < 24 := (hv 3) ▸ (Fin.isLt _)
  have hc' : newL q G1 G2 SI E 0 * 13824 + newL q G1 G2 SI E 1 * 576 + newL q G1 G2 SI E 2 * 24 +
      newL q G1 G2 SI E 3 = c := hc
  simp only [witOK, Bool.and_eq_true, wordEq_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [inG_gmB f hf, e1]; exact h1
  · rw [inG_gmB f hf, e2]; exact h2
  · funext l
    apply Fin.ext
    rw [hv l]
    fin_cases l
    · show newL q G1 G2 SI E 0 = c / 13824 % 24 % 24; omega
    · show newL q G1 G2 SI E 1 = c / 576 % 24 % 24; omega
    · show newL q G1 G2 SI E 2 = c / 24 % 24 % 24; omega
    · show newL q G1 G2 SI E 3 = c / 1 % 24 % 24; omega

/-! ### Lists of words -/

theorem witGoK_sound (f stop : ℕ) : ∀ (q : ℕ) (cs ws : List ℕ), witGoK f stop q cs ws = true →
    witGo f q cs ws = true ∧ q + cs.length = stop
  | q, c :: cs, wc :: ws, h => by
    simp only [witGoK, Bool.and_eq_true] at h
    have ih := witGoK_sound f stop (q + 1) cs ws h.2
    simp only [witGo, Bool.and_eq_true, List.length_cons]
    exact ⟨⟨witOKK_sound h.1, ih.1⟩, by omega⟩
  | q, [], [], h => by
    simp only [witGoK] at h
    exact ⟨rfl, by simpa using Nat.eq_of_beq_eq_true h⟩
  | _, [], _ :: _, h => by simp [witGoK] at h
  | _, _ :: _, [], h => by simp [witGoK] at h

theorem witGoK_append (f : ℕ) : ∀ (q mid stop : ℕ) (a c b d : List ℕ),
    witGoK f mid q a c = true → witGoK f stop mid b d = true → witGoK f stop q (a ++ b) (c ++ d) = true
  | q, mid, stop, [], [], b, d, h1, h2 => by
    simp only [witGoK] at h1
    rw [Nat.eq_of_beq_eq_true h1]
    exact h2
  | q, mid, stop, x :: a, y :: c, b, d, h1, h2 => by
    simp only [witGoK, Bool.and_eq_true] at h1
    simp only [List.cons_append, witGoK, Bool.and_eq_true]
    exact ⟨h1.1, witGoK_append f (Nat.succ q) mid stop a c b d h1.2 h2⟩
  | _, _, _, [], _ :: _, _, _, h1, _ => by simp [witGoK] at h1
  | _, _, _, _ :: _, [], _, _, h1, _ => by simp [witGoK] at h1

theorem witGoK_flatten (f N : ℕ) : ∀ (cs ws : List (List ℕ)) (q : ℕ), ws.length = cs.length →
    (∀ k < cs.length, witGoK f (q + (k + 1) * N) (q + k * N) (cs.getD k []) (ws.getD k []) = true) →
    witGoK f (q + cs.length * N) q cs.flatten ws.flatten = true
  | [], [], q, _, _ => by simp [witGoK]
  | s :: cs, t :: ws, q, hl, h => by
    simp only [List.flatten_cons, List.length_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.add_zero, List.getD_cons_zero] at h0
    refine witGoK_append f q (q + N) _ s t _ _ h0 ?_
    have := witGoK_flatten f N cs ws (q + N) (by simpa using hl) fun k hk => by
      have := h (k + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at this
      rwa [show q + N + (k + 1) * N = q + (k + 1 + 1) * N by ring,
        show q + N + k * N = q + (k + 1) * N by ring]
    rwa [show q + N + cs.length * N = q + (cs.length + 1) * N by ring] at this
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

theorem stripR_sound : ∀ (s l r : List ℕ), stripR s l = some r → l = s ++ r
  | [], l, r, h => by
    have e : stripR [] l = some l := rfl
    rw [e] at h
    cases h
    rfl
  | b :: s, [], r, h => by
    have e : stripR (b :: s) [] = none := rfl
    rw [e] at h
    cases h
  | b :: s, a :: as, r, h => by
    have e : stripR (b :: s) (a :: as) = cond (Nat.beq a b) (stripR s as) none := rfl
    rw [e] at h
    cases hab : Nat.beq a b
    · rw [hab] at h
      cases h
    · rw [hab] at h
      rw [Nat.eq_of_beq_eq_true hab, stripR_sound s as r h]
      rfl

theorem stripsR_sound : ∀ (ss : List (List ℕ)) (l : List ℕ), stripsR ss l = true → l = ss.flatten
  | [], [], _ => rfl
  | [], a :: l, h => by
    have e : stripsR [] (a :: l) = false := rfl
    rw [e] at h
    cases h
  | s :: ss, l, h => by
    have e : stripsR (s :: ss) l =
        @Option.casesOn (List ℕ) (fun _ => Bool) (stripR s l) false (fun r => stripsR ss r) := rfl
    rw [e] at h
    cases hs : stripR s l with
    | none =>
      rw [hs] at h
      cases h
    | some r =>
      rw [hs] at h
      rw [stripR_sound s l r hs, List.flatten_cons, stripsR_sound ss r h]

/-- **Chunked witness check**: if the class and witness lists are the concatenations of slices `cs`, `ws`, and
the chunk fact holds for every slice `k` (positions `k N .. (k+1) N - 1`), then `witCheck` holds. -/
theorem witCheck_of_slices (f N : ℕ) (cls wit : List ℕ) (cs ws : List (List ℕ))
    (hcls : cls = cs.flatten) (hwit : wit = ws.flatten) (hK : cs.length * N = 24 * slen)
    (hl : ws.length = cs.length)
    (h : ∀ k < cs.length, witGoK f ((k + 1) * N) (k * N) (cs.getD k []) (ws.getD k []) = true) :
    witCheck f cls wit = true := by
  have hg := witGoK_flatten f N cs ws 0 hl fun k hk => by
    rw [Nat.zero_add, Nat.zero_add]; exact h k hk
  rw [Nat.zero_add, hK, ← hcls, ← hwit] at hg
  obtain ⟨hgo, hlen⟩ := witGoK_sound f _ 0 cls wit hg
  rw [Nat.zero_add] at hlen
  unfold witCheck
  rw [hlen, beq_self_eq_true, Bool.true_and]
  exact hgo

end NPT.Cert.Ident

#print axioms NPT.Cert.Ident.witOKK_sound
#print axioms NPT.Cert.Ident.witCheck_of_slices
