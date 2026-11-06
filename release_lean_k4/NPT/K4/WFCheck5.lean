/-
NPT.K4.WFCheck5 — a computable checker for `WF5` with its soundness (`wfCheck5 C = true → WF5 C`), for use with
`decide` (five-family certificate).  As `NPT.Cert.WFCheck`, with the 25 rules of `ruleTab5`, families `< 5`, `Consistent5`
and the equality shapes of `StiefelShape5` / `MargShape5` (`stiefelOK` / `margOK` / `specEq` are reused).
-/
import NPT.K4.WF5
import NPT.Cert.WFCheck

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.K4

/-- Position lists agree with rule `i` of `ruleTab5`. -/
def kposOK5 (xs : List ℕ) (i : ℕ) : Bool := (List.finRange 4).all fun s => posOf xs s == (rule5 i).kp s
def lposOK5 (xs : List ℕ) (i : ℕ) : Bool := (List.finRange 4).all fun s => posOf xs s == (rule5 i).lp s

/-- The rule of `ruleTab5` matching entry `(r, s)` of type `t` (or 25 if none). -/
def riOf5 (t : TypeD) (r s : ℕ) : ℕ :=
  ((List.range 25).find? fun i =>
    kposOK5 (Sem.CertD.ruleOf t r s).kpos i && lposOK5 (Sem.CertD.ruleOf t r s).lpos i).getD 25

/-- The cut of a type (from entry `(0, 0)`). -/
def cutOf5 (t : TypeD) : ℕ := (rule5 (riOf5 t 0 0)).cut

/-- Check of one multiplier type, five families. -/
def typeOK5 (t : TypeD) : Bool :=
  decide (cutOf5 t ∈ cutsUsed) &&
  (List.finRange t.nrows).all fun r => (List.finRange t.nrows).all fun s =>
    decide (riOf5 t r s < 25) && decide ((rule5 (riOf5 t r s)).cut = cutOf5 t) &&
    kposOK5 (Sem.CertD.ruleOf t r s).kpos (riOf5 t r s) &&
    lposOK5 (Sem.CertD.ruleOf t r s).lpos (riOf5 t r s) &&
    decide ((Sem.CertD.ruleOf t r s).fam < 5) &&
    decide (Consistent5 (Sem.CertD.ruleOf t r s).fam (patOf t r) (patOf t s)
      (rule5 (riOf5 t r s)).kp (rule5 (riOf5 t r s)).lp)

/-- Equality shapes, five families. -/
def eqOK5 (k : ℕ) (g : EqGroupD) : Bool :=
  stiefelOK k g 0 0 || stiefelOK k g 1 0 || stiefelOK k g 3 0 || stiefelOK k g 2 1 ||
  margOK k g 0 2 1 2 || margOK k g 1 3 2 4 || margOK k g 0 1 3 1 || margOK k g 2 1 4 1

/-- **The well-formedness checker, five families.** -/
def wfCheck5 (C : CertD) : Bool :=
  decide (1 ≤ C.k) && decide (2 ≤ C.d) && C.types.all typeOK5 && C.eqs.all (eqOK5 C.k)

lemma stiefelOK_spec5 {C : CertD} {g : EqGroupD} {f c : ℕ}
    (hfc : ((f = 0 ∨ f = 1 ∨ f = 3) ∧ c = 0) ∨ (f = 2 ∧ c = 1)) (h : stiefelOK C.k g f c = true) :
    StiefelShape5 C g := by
  unfold stiefelOK at h
  split at h
  · rename_i P hP
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨f, c, hfc, P, hP, h1, h2, fun l => specEq_spec (h3 l)⟩
  · exact absurd h (by simp)

lemma margOK_spec5 {C : CertD} {g : EqGroupD} {f1 c1 f2 c2 : ℕ}
    (hfc : (f1 = 0 ∧ c1 = 2 ∧ f2 = 1 ∧ c2 = 2) ∨ (f1 = 1 ∧ c1 = 3 ∧ f2 = 2 ∧ c2 = 4) ∨
      (f1 = 0 ∧ c1 = 1 ∧ f2 = 3 ∧ c2 = 1) ∨ (f1 = 2 ∧ c1 = 1 ∧ f2 = 4 ∧ c2 = 1))
    (h : margOK C.k g f1 c1 f2 c2 = true) : MargShape5 C g := by
  unfold margOK at h
  split at h
  · rename_i P1 P2 hP
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨f1, c1, f2, c2, hfc, P1, P2, hP, h1, h2, h3, h4, fun l => ⟨specEq_spec (h5 l).1.1, ?_⟩⟩
    rw [specEq_spec (h5 l).1.2, (h5 l).2]
  · exact absurd h (by simp)

theorem wfCheck5_sound {C : CertD} (h : wfCheck5 C = true) : WF5 C := by
  simp only [wfCheck5, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hk, hd⟩, ht⟩, he⟩ := h
  refine ⟨hk, hd, fun t htm => ?_, fun g hg => ?_⟩
  · have h := ht t htm
    simp only [typeOK5, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies] at h
    obtain ⟨hS, hrs⟩ := h
    refine ⟨fun r s => riOf5 t r.val s.val, cutOf5 t, hS, fun r s => (hrs r s).1.1.1.1.1,
      fun r s => (hrs r s).1.1.1.1.2, fun r s => ?_, fun r s => ?_, fun r s => (hrs r s).1.2,
      fun r s => (hrs r s).2⟩
    · have hk := (hrs r s).1.1.1.2
      simp only [kposOK5, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hk
      exact funext hk
    · have hl := (hrs r s).1.1.2
      simp only [lposOK5, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hl
      exact funext hl
  · have h := he g hg
    simp only [eqOK5, Bool.or_eq_true] at h
    rcases h with (((((((h | h) | h) | h) | h) | h) | h) | h)
    · exact Or.inl (stiefelOK_spec5 (Or.inl ⟨Or.inl rfl, rfl⟩) h)
    · exact Or.inl (stiefelOK_spec5 (Or.inl ⟨Or.inr (Or.inl rfl), rfl⟩) h)
    · exact Or.inl (stiefelOK_spec5 (Or.inl ⟨Or.inr (Or.inr rfl), rfl⟩) h)
    · exact Or.inl (stiefelOK_spec5 (Or.inr ⟨rfl, rfl⟩) h)
    · exact Or.inr (margOK_spec5 (Or.inl ⟨rfl, rfl, rfl, rfl⟩) h)
    · exact Or.inr (margOK_spec5 (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) h)
    · exact Or.inr (margOK_spec5 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩))) h)
    · exact Or.inr (margOK_spec5 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))) h)

end NPT.K4

#print axioms NPT.K4.wfCheck5_sound
