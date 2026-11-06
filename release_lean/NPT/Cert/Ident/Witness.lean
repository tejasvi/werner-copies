/-
NPT.Cert.Ident.Witness — per-word orbit witnesses for `Sem.IdFact`: class representative codes and
witness codes `((g1·24 + g2)·6 + σ)·2 + ε` per word position, and their check.
-/
import NPT.Cert.Ident.IdFactGen

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-- The word with ep3core code `c = w0·24³ + w1·24² + w2·24 + w3`. -/
def wordOfCode (c : ℕ) : Fin 4 → Fin 24 := fun l => Fin.ofNat 24 (c / 24 ^ (3 - l.val) % 24)

/-- The permutations of `Fin 3` in itertools order (`σ j` = entry `j`). -/
def s3L : List (List ℕ) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
def s3F (i : ℕ) : Fin 3 → Fin 3 := fun j => Fin.ofNat 3 ((s3L.getD i []).getD j.val 0)

lemma s3F_bij : ∀ i : Fin 6, Function.Bijective (s3F i.val) := by decide

/-- Decode a witness code. -/
def decWit (c : ℕ) : Fin 24 × Fin 24 × (Fin 3 → Fin 3) × Bool :=
  (Fin.ofNat 24 (c / 288 % 24), Fin.ofNat 24 (c / 12 % 24), s3F (c / 2 % 6), c % 2 == 1)

lemma decWit_bij (c : ℕ) : Function.Bijective (decWit c).2.2.1 :=
  s3F_bij ⟨c / 2 % 6, Nat.mod_lt _ (by norm_num)⟩

def wordEq (a b : Fin 4 → Fin 24) : Bool := (List.finRange 4).all fun l => a l == b l

lemma wordEq_iff (a b : Fin 4 → Fin 24) : wordEq a b = true ↔ a = b := by
  simp only [wordEq, List.all_eq_true, List.mem_finRange, beq_iff_eq, true_implies]
  exact ⟨fun h => funext h, fun h l => h ▸ rfl⟩

/-- Check of the word at position `q` with class code `c` and witness code `wc`. -/
def witOK (f q c wc : ℕ) : Bool :=
  inG f (decWit wc).1 && inG f (decWit wc).2.1 &&
    wordEq (act (decWit wc).1 (decWit wc).2.1 (decWit wc).2.2.1 (decWit wc).2.2.2 (wordAt q)) (wordOfCode c)

def witGo (f : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | q, c :: cs, wc :: ws => witOK f q c wc && witGo f (q + 1) cs ws
  | _, [], [] => true
  | _, _, _ => false

/-- The witness check of family `f`. -/
def witCheck (f : ℕ) (cls wit : List ℕ) : Bool := (cls.length == 24 * slen) && witGo f 0 cls wit

lemma witGo_spec (f : ℕ) : ∀ (q0 : ℕ) (cs ws : List ℕ), witGo f q0 cs ws = true →
    ∀ i < cs.length, witOK f (q0 + i) (cs.getD i 0) (ws.getD i 0) = true
  | q0, c :: cs, wc :: ws, h, 0, _ => by
    simp only [witGo, Bool.and_eq_true] at h; simpa using h.1
  | q0, c :: cs, wc :: ws, h, i + 1, hi => by
    simp only [witGo, Bool.and_eq_true] at h
    have := witGo_spec f (q0 + 1) cs ws h.2 i (by simpa using hi)
    simpa [show q0 + (i + 1) = q0 + 1 + i by omega] using this
  | _, [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _, _ :: _, [], h, _, _ => by simp [witGo] at h

lemma witCheck_spec (f : ℕ) (cls wit : List ℕ) (h : witCheck f cls wit = true) (w : Fin 4 → Fin 24) :
    witOK f (posW w) (cls.getD (posW w) 0) (wit.getD (posW w) 0) = true := by
  simp only [witCheck, Bool.and_eq_true, beq_iff_eq] at h
  have := witGo_spec f 0 cls wit h.2 (posW w) (by rw [h.1]; exact posW_lt w)
  simpa using this

/-- The witness fields of a word, from the witness check. -/
lemma witCheck_fields (f : ℕ) (cls wit : List ℕ) (h : witCheck f cls wit = true) (w : Fin 4 → Fin 24) :
    inG f (decWit (wit.getD (posW w) 0)).1 = true ∧ inG f (decWit (wit.getD (posW w) 0)).2.1 = true ∧
      act (decWit (wit.getD (posW w) 0)).1 (decWit (wit.getD (posW w) 0)).2.1 (decWit (wit.getD (posW w) 0)).2.2.1
        (decWit (wit.getD (posW w) 0)).2.2.2 w = wordOfCode (cls.getD (posW w) 0) := by
  have h1 := witCheck_spec f cls wit h w
  simp only [witOK, Bool.and_eq_true, wordEq_iff, wordAt_posW] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

end NPT.Cert.Ident
