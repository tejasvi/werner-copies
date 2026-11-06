/-
NPT.K4.WitnessS4 — the orbit-witness check for the families 3 = '40' (aaaa) and 4 = '04' (bbbb), whose group
`G_f` is all of S4 (membership: `NPT.K4.inG5` of `NPT.K4.Phys5` is `true` there): the act-equation of
`witOK5` without the membership tests (`witOKS`, `witCheckS`, `witCheckS_fields`), its kernel form `witOKKS` / `witGoKS`
with soundness, and the slice and code-bound lemmas of `NPT.K4.WitnessK5` / `NPT.K4.WitnessK5Lt`.
-/
import NPT.K4.WitnessK5Lt

open NPT.Cert.Sem NPT.Brauer NPT.Cert.Ident

namespace NPT.K4

/-! ### The check (G = S4) -/

/-- Check of the word at position `q` with class code `c` and witness code `wc`: the acted word is the word at `c`. -/
def witOKS (q c wc : ℕ) : Bool :=
  wordEq5 (act (decWit5 wc).1 (decWit5 wc).2.1 (decWit5 wc).2.2.1 (decWit5 wc).2.2.2 (wordAt5 q)) (wordAt5 c)

def witGoS : ℕ → List ℕ → List ℕ → Bool
  | q, c :: cs, wc :: ws => witOKS q c wc && witGoS (q + 1) cs ws
  | _, [], [] => true
  | _, _, _ => false

/-- The witness check of an S4 family over all `24^5` words. -/
def witCheckS (cls wit : List ℕ) : Bool := (cls.length == 24 * slen5) && witGoS 0 cls wit

lemma witGoS_spec : ∀ (q0 : ℕ) (cs ws : List ℕ), witGoS q0 cs ws = true →
    ∀ i < cs.length, witOKS (q0 + i) (cs.getD i 0) (ws.getD i 0) = true
  | q0, c :: cs, wc :: ws, h, 0, _ => by
    simp only [witGoS, Bool.and_eq_true] at h; simpa using h.1
  | q0, c :: cs, wc :: ws, h, i + 1, hi => by
    simp only [witGoS, Bool.and_eq_true] at h
    have := witGoS_spec (q0 + 1) cs ws h.2 i (by simpa using hi)
    simpa [show q0 + (i + 1) = q0 + 1 + i by omega] using this
  | _, [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | _, _ :: _, [], h, _, _ => by simp [witGoS] at h

lemma witCheckS_spec (cls wit : List ℕ) (h : witCheckS cls wit = true) (w : Fin 5 → Fin 24) :
    witOKS (posW5 w) (cls.getD (posW5 w) 0) (wit.getD (posW5 w) 0) = true := by
  simp only [witCheckS, Bool.and_eq_true, beq_iff_eq] at h
  have := witGoS_spec 0 cls wit h.2 (posW5 w) (by rw [h.1]; exact posW5_lt w)
  simpa using this

/-- **The witness field of a word** (G = S4): the group element moves the word to the representative of its class. -/
theorem witCheckS_fields (cls wit : List ℕ) (h : witCheckS cls wit = true) (w : Fin 5 → Fin 24) :
    act (decWit5 (wit.getD (posW5 w) 0)).1 (decWit5 (wit.getD (posW5 w) 0)).2.1
      (decWit5 (wit.getD (posW5 w) 0)).2.2.1 (decWit5 (wit.getD (posW5 w) 0)).2.2.2 w =
      wordAt5 (cls.getD (posW5 w) 0) := by
  have h1 := witCheckS_spec cls wit h w
  simp only [witOKS, wordEq5_iff, wordAt5_posW5] at h1
  exact h1

/-! ### Kernel form -/

/-- Kernel check of the word at position `q` with class code `c` and witness code `wc` (`witOKK5` without `gmB`). -/
def witOKKS (q c wc : Nat) : Bool :=
  let e := Nat.mod wc 2
  let si := Nat.mod (Nat.div wc 2) 24
  let g2 := Nat.mod (Nat.div wc 48) 24
  let g1 := Nat.mod (Nat.div wc 1152) 24
  Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (newL5 q g1 g2 si e 4) 331776)
    (Nat.mul (newL5 q g1 g2 si e 3) 13824)) (Nat.mul (newL5 q g1 g2 si e 2) 576))
    (Nat.mul (newL5 q g1 g2 si e 1) 24)) (newL5 q g1 g2 si e 0)) c

/-- Check positions `q, q + 1, …` and that the lists end together at position `stop`. -/
def witGoKS (stop : Nat) : Nat → List Nat → List Nat → Bool
  | q, c :: cs, wc :: ws => witOKKS q c wc && witGoKS stop (Nat.succ q) cs ws
  | q, [], [] => Nat.beq q stop
  | _, _, _ => false

/-- The decoded witness acts on the word at `q` digit by digit as the kernel tables say, and the code is a position. -/
lemma witOKKS_val {q c wc : ℕ} (h : witOKKS q c wc = true) :
    (∀ l : Fin 5, (act (decWit5 wc).1 (decWit5 wc).2.1 (decWit5 wc).2.2.1 (decWit5 wc).2.2.2 (wordAt5 q) l).val =
      c / 24 ^ l.val % 24) ∧ c < 24 * slen5 := by
  simp only [witOKKS] at h
  have hc := Nat.eq_of_beq_eq_true h
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
  refine ⟨fun l => ?_, by unfold slen5; omega⟩
  rw [hv l]
  fin_cases l
  · show newL5 q G1 G2 SI E 0 = c / 1 % 24; omega
  · show newL5 q G1 G2 SI E 1 = c / 24 % 24; omega
  · show newL5 q G1 G2 SI E 2 = c / 576 % 24; omega
  · show newL5 q G1 G2 SI E 3 = c / 13824 % 24; omega
  · show newL5 q G1 G2 SI E 4 = c / 331776 % 24; omega

theorem witOKKS_sound {q c wc : ℕ} (h : witOKKS q c wc = true) : witOKS q c wc = true := by
  simp only [witOKS, wordEq5_iff]
  funext l
  apply Fin.ext
  rw [(witOKKS_val h).1 l]
  show c / 24 ^ l.val % 24 = c / 24 ^ l.val % 24 % 24
  rw [Nat.mod_mod]

theorem witOKKS_lt {q c wc : ℕ} (h : witOKKS q c wc = true) : c < 24 * slen5 := (witOKKS_val h).2

/-! ### Lists of words -/

theorem witGoKS_sound (stop : ℕ) : ∀ (q : ℕ) (cs ws : List ℕ), witGoKS stop q cs ws = true →
    witGoS q cs ws = true ∧ q + cs.length = stop
  | q, c :: cs, wc :: ws, h => by
    simp only [witGoKS, Bool.and_eq_true] at h
    have ih := witGoKS_sound stop (q + 1) cs ws h.2
    simp only [witGoS, Bool.and_eq_true, List.length_cons]
    exact ⟨⟨witOKKS_sound h.1, ih.1⟩, by omega⟩
  | q, [], [], h => by
    simp only [witGoKS] at h
    exact ⟨rfl, by simpa using Nat.eq_of_beq_eq_true h⟩
  | _, [], _ :: _, h => by simp [witGoKS] at h
  | _, _ :: _, [], h => by simp [witGoKS] at h

theorem witGoKS_append : ∀ (q mid stop : ℕ) (a c b d : List ℕ),
    witGoKS mid q a c = true → witGoKS stop mid b d = true → witGoKS stop q (a ++ b) (c ++ d) = true
  | q, mid, stop, [], [], b, d, h1, h2 => by
    simp only [witGoKS] at h1
    rw [Nat.eq_of_beq_eq_true h1]
    exact h2
  | q, mid, stop, x :: a, y :: c, b, d, h1, h2 => by
    simp only [witGoKS, Bool.and_eq_true] at h1
    simp only [List.cons_append, witGoKS, Bool.and_eq_true]
    exact ⟨h1.1, witGoKS_append (Nat.succ q) mid stop a c b d h1.2 h2⟩
  | _, _, _, [], _ :: _, _, _, h1, _ => by simp [witGoKS] at h1
  | _, _, _, _ :: _, [], _, _, h1, _ => by simp [witGoKS] at h1

theorem witGoKS_flatten (N : ℕ) : ∀ (cs ws : List (List ℕ)) (q : ℕ), ws.length = cs.length →
    (∀ k < cs.length, witGoKS (q + (k + 1) * N) (q + k * N) (cs.getD k []) (ws.getD k []) = true) →
    witGoKS (q + cs.length * N) q cs.flatten ws.flatten = true
  | [], [], q, _, _ => by simp [witGoKS]
  | s :: cs, t :: ws, q, hl, h => by
    simp only [List.flatten_cons, List.length_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.zero_add, Nat.one_mul, Nat.zero_mul, Nat.add_zero, List.getD_cons_zero] at h0
    refine witGoKS_append q (q + N) _ s t _ _ h0 ?_
    have := witGoKS_flatten N cs ws (q + N) (by simpa using hl) fun k hk => by
      have := h (k + 1) (by simp; omega)
      simp only [List.getD_cons_succ] at this
      rwa [show q + N + (k + 1) * N = q + (k + 1 + 1) * N by ring,
        show q + N + k * N = q + (k + 1) * N by ring]
    rwa [show q + N + cs.length * N = q + (cs.length + 1) * N by ring] at this
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- Every class code of a checked list of words is a position. -/
theorem witGoKS_lt (stop : ℕ) : ∀ (q : ℕ) (cs ws : List ℕ), witGoKS stop q cs ws = true →
    ∀ c ∈ cs, c < 24 * slen5
  | q, c :: cs, wc :: ws, h, x, hx => by
    simp only [witGoKS, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact witOKKS_lt h.1
    · exact witGoKS_lt stop (Nat.succ q) cs ws h.2 x hx
  | _, [], _, _, _, hx => absurd hx (List.not_mem_nil)
  | _, _ :: _, [], h, _, _ => by simp [witGoKS] at h

/-- **Chunked witness check with the code bound** (G = S4): slice facts give `witCheckS` and `c < 24^5` for every
class code. -/
theorem witCheckS_of_slices_lt (N : ℕ) (cls wit : List ℕ) (cs ws : List (List ℕ))
    (hcls : cls = cs.flatten) (hwit : wit = ws.flatten) (hK : cs.length * N = 24 * slen5)
    (hl : ws.length = cs.length)
    (h : ∀ k < cs.length, witGoKS ((k + 1) * N) (k * N) (cs.getD k []) (ws.getD k []) = true) :
    witCheckS cls wit = true ∧ ∀ c ∈ cls, c < 24 * slen5 := by
  have hg := witGoKS_flatten N cs ws 0 hl fun k hk => by
    rw [Nat.zero_add, Nat.zero_add]; exact h k hk
  rw [Nat.zero_add, hK, ← hcls, ← hwit] at hg
  obtain ⟨hgo, hlen⟩ := witGoKS_sound _ 0 cls wit hg
  rw [Nat.zero_add] at hlen
  refine ⟨?_, witGoKS_lt _ 0 cls wit hg⟩
  unfold witCheckS
  rw [hlen, beq_self_eq_true, Bool.true_and]
  exact hgo

end NPT.K4
