/-
NPT.K4.Witness5 — per-word orbit witnesses for five legs (k = 4, words `Fin 5 → Fin 24`; the k = 3 version is
`NPT.Cert.Ident.Witness`): word positions (leg 4 slowest), class codes (the position of the class representative),
witness codes `((g1·24 + g2)·24 + s)·2 + ε` (`σ = s4F s`, permutation number `s` of the four sites), and their check
`witCheck5`, whose consequence `witCheck5_fields` gives the orbit-witness fields of `Sem.IdFact` at `k = 4`.
-/
import NPT.Cert.Sem

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.K4

/-- Words per value of the auxiliary leg (`24^4`). -/
def slen5 : ℕ := 331776

/-- Position of a word: leg 4 (auxiliary) slowest, leg 0 fastest. -/
def posW5 (w : Fin 5 → Fin 24) : ℕ :=
  (w 4).val * 331776 + (w 3).val * 13824 + (w 2).val * 576 + (w 1).val * 24 + (w 0).val

/-- The word at a position (also the decoding of class codes). -/
def wordAt5 (q : ℕ) : Fin 5 → Fin 24 := fun l => Fin.ofNat 24 (q / 24 ^ l.val % 24)

lemma posW5_lt (w : Fin 5 → Fin 24) : posW5 w < 24 * slen5 := by
  unfold posW5 slen5
  have := (w 0).isLt; have := (w 1).isLt; have := (w 2).isLt; have := (w 3).isLt; have := (w 4).isLt
  omega

lemma wordAt5_posW5 (w : Fin 5 → Fin 24) : wordAt5 (posW5 w) = w := by
  funext l
  apply Fin.ext
  have h0 := (w 0).isLt; have h1 := (w 1).isLt; have h2 := (w 2).isLt; have h3 := (w 3).isLt
  have h4 := (w 4).isLt
  fin_cases l <;> simp [wordAt5, posW5, Fin.val_ofNat] <;> omega

/-- Permutation number `i` of the four sites (itertools order, `NPT.Brauer.permL`): `σ j` = entry `j`. -/
def s4F (i : ℕ) : Fin 4 → Fin 4 := fun j => Fin.ofNat 4 ((permL.getD i []).getD j.val 0)

lemma s4F_bij : ∀ i : Fin 24, Function.Bijective (s4F i.val) := by decide

/-- Decode a witness code. -/
def decWit5 (c : ℕ) : Fin 24 × Fin 24 × (Fin 4 → Fin 4) × Bool :=
  (Fin.ofNat 24 (c / 1152 % 24), Fin.ofNat 24 (c / 48 % 24), s4F (c / 2 % 24), c % 2 == 1)

lemma decWit5_bij (c : ℕ) : Function.Bijective (decWit5 c).2.2.1 :=
  s4F_bij ⟨c / 2 % 24, Nat.mod_lt _ (by norm_num)⟩

def wordEq5 (a b : Fin 5 → Fin 24) : Bool := (List.finRange 5).all fun l => a l == b l

lemma wordEq5_iff (a b : Fin 5 → Fin 24) : wordEq5 a b = true ↔ a = b := by
  simp only [wordEq5, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies]
  exact ⟨fun h => funext h, fun h l => h ▸ rfl⟩

/-- Check of the word at position `q` with class code `c` and witness code `wc`. -/
def witOK5 (f q c wc : ℕ) : Bool :=
  inG f (decWit5 wc).1 && inG f (decWit5 wc).2.1 &&
    wordEq5 (act (decWit5 wc).1 (decWit5 wc).2.1 (decWit5 wc).2.2.1 (decWit5 wc).2.2.2 (wordAt5 q)) (wordAt5 c)

def witGo5 (f : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | q, c :: cs, wc :: ws => witOK5 f q c wc && witGo5 f (q + 1) cs ws
  | _, [], [] => true
  | _, _, _ => false

/-- The witness check of family `f` over all `24^5` words. -/
def witCheck5 (f : ℕ) (cls wit : List ℕ) : Bool := (cls.length == 24 * slen5) && witGo5 f 0 cls wit

lemma witGo5_spec (f : ℕ) : ∀ (q0 : ℕ) (cs ws : List ℕ), witGo5 f q0 cs ws = true →
    ∀ i < cs.length, witOK5 f (q0 + i) (cs.getD i 0) (ws.getD i 0) = true
  | q0, c :: cs, wc :: ws, h, 0, _ => by
    simp only [witGo5, Bool.and_eq_true] at h; simpa using h.1
  | q0, c :: cs, wc :: ws, h, i + 1, hi => by
    simp only [witGo5, Bool.and_eq_true] at h
    have := witGo5_spec f (q0 + 1) cs ws h.2 i (by simpa using hi)
    simpa [show q0 + (i + 1) = q0 + 1 + i by omega] using this
  | _, [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _, _ :: _, [], h, _, _ => by simp [witGo5] at h

lemma witCheck5_spec (f : ℕ) (cls wit : List ℕ) (h : witCheck5 f cls wit = true) (w : Fin 5 → Fin 24) :
    witOK5 f (posW5 w) (cls.getD (posW5 w) 0) (wit.getD (posW5 w) 0) = true := by
  simp only [witCheck5, Bool.and_eq_true, beq_iff_eq] at h
  have := witGo5_spec f 0 cls wit h.2 (posW5 w) (by rw [h.1]; exact posW5_lt w)
  simpa using this

/-- **The witness fields of a word**, from the witness check: `g1, g2 ∈ G_f` and the group element moves the word to
the representative of its class. -/
theorem witCheck5_fields (f : ℕ) (cls wit : List ℕ) (h : witCheck5 f cls wit = true) (w : Fin 5 → Fin 24) :
    inG f (decWit5 (wit.getD (posW5 w) 0)).1 = true ∧ inG f (decWit5 (wit.getD (posW5 w) 0)).2.1 = true ∧
      act (decWit5 (wit.getD (posW5 w) 0)).1 (decWit5 (wit.getD (posW5 w) 0)).2.1
        (decWit5 (wit.getD (posW5 w) 0)).2.2.1 (decWit5 (wit.getD (posW5 w) 0)).2.2.2 w =
        wordAt5 (cls.getD (posW5 w) 0) := by
  have h1 := witCheck5_spec f cls wit h w
  simp only [witOK5, Bool.and_eq_true, wordEq5_iff, wordAt5_posW5] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

end NPT.K4
