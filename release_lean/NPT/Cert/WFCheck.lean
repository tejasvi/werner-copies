/-
NPT.Cert.WFCheck — a computable checker for the well-formedness conditions `WF` of the soundness theorem,
with its soundness (`wfCheck C = true → WF C`), for use with `decide`.
-/
import NPT.Cert.Soundness

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem
open scoped ComplexOrder

namespace NPT.Cert

/-- Position lists agree with rule `i`. -/
def kposOK (xs : List ℕ) (i : ℕ) : Bool := (List.finRange 4).all fun s => posOf xs s == rkp i s
def lposOK (xs : List ℕ) (i : ℕ) : Bool := (List.finRange 4).all fun s => posOf xs s == rlp i s

/-- The verified rule matching entry `(r, s)` of type `t` (or `nRules` if none). -/
def riOf (t : TypeD) (r s : ℕ) : ℕ :=
  ((List.range nRules).find? fun i =>
    kposOK (Sem.CertD.ruleOf t r s).kpos i && lposOK (Sem.CertD.ruleOf t r s).lpos i).getD nRules

/-- The cut of a type (from entry `(0, 0)`). -/
def cutOf (t : TypeD) : ℕ := rcut (riOf t 0 0)

/-- Check of one multiplier type. -/
def typeOK (t : TypeD) : Bool :=
  decide (cutOf t ∈ cutsUsed) &&
  (List.finRange t.nrows).all fun r => (List.finRange t.nrows).all fun s =>
    decide (riOf t r s < nRules) && decide (rcut (riOf t r s) = cutOf t) &&
    kposOK (Sem.CertD.ruleOf t r s).kpos (riOf t r s) &&
    lposOK (Sem.CertD.ruleOf t r s).lpos (riOf t r s) &&
    decide ((Sem.CertD.ruleOf t r s).fam < 3) &&
    decide (Phys.Consistent (Sem.CertD.ruleOf t r s).fam (patOf t r) (patOf t s)
      (rkp (riOf t r s)) (rlp (riOf t r s)))

/-- Fieldwise comparison of an equality spec with `specOf c kind mk`. -/
def specEq (sp : EqSpecD) (c kind : ℕ) : Bool :=
  sp.slot == sget c 0 && sp.order == [sget c 1, sget c 2, sget c 3] && sp.kind == kind

lemma specEq_spec {sp : EqSpecD} {c kind : ℕ} (h : specEq sp c kind = true) : sp = specOf c kind sp.mkeys := by
  simp only [specEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases sp
  simp only [specOf] at *
  subst h1 h2 h3
  rfl

/-- Check of a Stiefel-shaped group with `(f, c)`. -/
def stiefelOK (k : ℕ) (g : EqGroupD) (f c : ℕ) : Bool :=
  match g.parts with
  | [P] => P.fam == f && P.sign == 1 &&
      (List.finRange (k + 1)).all fun l => specEq (P.specs.getD l.val default) c (if l.val < k then 0 else 1)
  | _ => false

/-- Check of a marginal-shaped group with `(f1, c1, f2, c2)`. -/
def margOK (k : ℕ) (g : EqGroupD) (f1 c1 f2 c2 : ℕ) : Bool :=
  match g.parts with
  | [P1, P2] => P1.fam == f1 && P1.sign == 1 && P2.fam == f2 && P2.sign == -1 &&
      (List.finRange (k + 1)).all fun l => specEq (P1.specs.getD l.val default) c1 0 &&
        specEq (P2.specs.getD l.val default) c2 0 &&
        (P2.specs.getD l.val default).mkeys == (P1.specs.getD l.val default).mkeys
  | _ => false

def eqOK (k : ℕ) (g : EqGroupD) : Bool :=
  stiefelOK k g 0 0 || stiefelOK k g 1 0 || stiefelOK k g 2 1 || margOK k g 0 2 1 2 || margOK k g 1 3 2 4

/-- **The well-formedness checker.** -/
def wfCheck (C : CertD) : Bool :=
  decide (1 ≤ C.k) && decide (2 ≤ C.d) && C.types.all typeOK && C.eqs.all (eqOK C.k)

lemma stiefelOK_spec {C : CertD} {g : EqGroupD} {f c : ℕ}
    (hfc : ((f = 0 ∨ f = 1) ∧ c = 0) ∨ (f = 2 ∧ c = 1)) (h : stiefelOK C.k g f c = true) :
    StiefelShape C g := by
  unfold stiefelOK at h
  split at h
  · rename_i P hP
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨f, c, hfc, P, hP, h1, h2, fun l => specEq_spec (h3 l)⟩
  · exact absurd h (by simp)

lemma margOK_spec {C : CertD} {g : EqGroupD} {f1 c1 f2 c2 : ℕ}
    (hfc : (f1 = 0 ∧ c1 = 2 ∧ f2 = 1 ∧ c2 = 2) ∨ (f1 = 1 ∧ c1 = 3 ∧ f2 = 2 ∧ c2 = 4))
    (h : margOK C.k g f1 c1 f2 c2 = true) : MargShape C g := by
  unfold margOK at h
  split at h
  · rename_i P1 P2 hP
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨f1, c1, f2, c2, hfc, P1, P2, hP, h1, h2, h3, h4, fun l => ⟨specEq_spec (h5 l).1.1, ?_⟩⟩
    rw [specEq_spec (h5 l).1.2, (h5 l).2]
  · exact absurd h (by simp)

theorem wfCheck_sound {C : CertD} (h : wfCheck C = true) : WF C := by
  simp only [wfCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hk, hd⟩, ht⟩, he⟩ := h
  refine ⟨hk, hd, fun t htm => ?_, fun g hg => ?_⟩
  · have h := ht t htm
    simp only [typeOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
      true_implies] at h
    obtain ⟨hS, hrs⟩ := h
    refine ⟨fun r s => riOf t r.val s.val, cutOf t, hS, fun r s => (hrs r s).1.1.1.1.1,
      fun r s => (hrs r s).1.1.1.1.2, fun r s => ?_, fun r s => ?_, fun r s => (hrs r s).1.2,
      fun r s => (hrs r s).2⟩
    · have hk := (hrs r s).1.1.1.2
      simp only [kposOK, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hk
      exact funext hk
    · have hl := (hrs r s).1.1.2
      simp only [lposOK, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at hl
      exact funext hl
  · have h := he g hg
    simp only [eqOK, Bool.or_eq_true] at h
    rcases h with (((h | h) | h) | h) | h
    · exact Or.inl (stiefelOK_spec (Or.inl ⟨Or.inl rfl, rfl⟩) h)
    · exact Or.inl (stiefelOK_spec (Or.inl ⟨Or.inr rfl, rfl⟩) h)
    · exact Or.inl (stiefelOK_spec (Or.inr ⟨rfl, rfl⟩) h)
    · exact Or.inr (margOK_spec (Or.inl ⟨rfl, rfl, rfl, rfl⟩) h)
    · exact Or.inr (margOK_spec (Or.inr ⟨rfl, rfl, rfl, rfl⟩) h)

/-- PSD of every block of the list implies the PSD hypothesis of the soundness theorem. -/
lemma blkZ_psd_of {C : CertD} (h : ∀ b ∈ C.Z, (b.Zmat C.Lden).PosSemidef) :
    ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef := by
  intro t _
  unfold Sem.CertD.blkZ
  by_cases hz : t.zi < C.Z.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz, Option.getD_some]
    exact h _ (List.getElem_mem hz)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    have hn : (default : NPT.Cert.PBlock).n = 0 := rfl
    have hz0 : (default : NPT.Cert.PBlock).Zmat C.Lden = 0 := by
      ext i j; exact absurd (i.isLt.trans_eq hn) (Nat.not_lt_zero _)
    rw [hz0]
    exact Matrix.PosSemidef.zero

/-- **Soundness with the computable checker.** -/
theorem soundness_of_check (C : CertD) [NeZero C.d] (hwf : wfCheck C = true) (hid : IdFact C)
    (hpsd : ∀ b ∈ C.Z, (b.Zmat C.Lden).PosSemidef) : NPT.EP (Fin C.k) C.d (1 / 2) :=
  soundness C (wfCheck_sound hwf) hid (blkZ_psd_of hpsd)

end NPT.Cert

#print axioms NPT.Cert.soundness_of_check
