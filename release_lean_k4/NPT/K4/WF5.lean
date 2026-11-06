/-
NPT.K4.WF5 — well-formedness of a five-family certificate and the new physical equalities (five-family certificate).

* `StiefelShape5`, `MargShape5`: the equality shapes of `NPT.Cert.WF` plus `stiefel40` (family 40, traced slot
  code 0) and the marginals `aaa` (31 vs 40) and `bbb` (13 vs 04), traced slot code 1 (slot 3, survivors 0, 1, 2).
* `WF5`: as `NPT.Cert.WF`, with entry rules from `ruleTab5` (25 rules, `rule5`), families `< 5`, `Consistent5`.
* `stiefel40_phys`, `aaa_phys`, `bbb_phys`: the physical facts behind the new equality groups (proofs from
  `NPT.Cert.Phys.Stiefel.applyG_stF_patVec` and `NPT.Cert.Phys.Marg.applyG_delK_rank1`).
-/
import NPT.K4.RuleData5
import NPT.K4.Phys5
import NPT.Cert.Soundness

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Phys

namespace NPT.K4

/-- Stiefel-shaped equality group, five families. -/
def StiefelShape5 (C : CertD) (g : EqGroupD) : Prop :=
  ∃ f c : ℕ, (((f = 0 ∨ f = 1 ∨ f = 3) ∧ c = 0) ∨ (f = 2 ∧ c = 1)) ∧ ∃ P, g.parts = [P] ∧ P.fam = f ∧ P.sign = 1 ∧
    ∀ l : Fin (C.k + 1), P.specs.getD l.val default =
      specOf c (if l.val < C.k then 0 else 1) (P.specs.getD l.val default).mkeys

/-- Marginal-shaped equality group, five families. -/
def MargShape5 (C : CertD) (g : EqGroupD) : Prop :=
  ∃ f1 c1 f2 c2 : ℕ, ((f1 = 0 ∧ c1 = 2 ∧ f2 = 1 ∧ c2 = 2) ∨ (f1 = 1 ∧ c1 = 3 ∧ f2 = 2 ∧ c2 = 4) ∨
      (f1 = 0 ∧ c1 = 1 ∧ f2 = 3 ∧ c2 = 1) ∨ (f1 = 2 ∧ c1 = 1 ∧ f2 = 4 ∧ c2 = 1)) ∧
    ∃ P1 P2, g.parts = [P1, P2] ∧ P1.fam = f1 ∧ P1.sign = 1 ∧ P2.fam = f2 ∧ P2.sign = -1 ∧
      ∀ l : Fin (C.k + 1), P1.specs.getD l.val default = specOf c1 0 (P1.specs.getD l.val default).mkeys ∧
        P2.specs.getD l.val default = specOf c2 0 (P1.specs.getD l.val default).mkeys

/-- **Well-formedness, five families.** -/
structure WF5 (C : CertD) : Prop where
  hk : 1 ≤ C.k
  hd : 2 ≤ C.d
  types : ∀ t ∈ C.types, ∃ ri : Fin t.nrows → Fin t.nrows → ℕ, ∃ S ∈ cutsUsed,
    (∀ r s, ri r s < 25) ∧ (∀ r s, (rule5 (ri r s)).cut = S) ∧
    (∀ r s : Fin t.nrows, posOf (Sem.CertD.ruleOf t r.val s.val).kpos = (rule5 (ri r s)).kp) ∧
    (∀ r s : Fin t.nrows, posOf (Sem.CertD.ruleOf t r.val s.val).lpos = (rule5 (ri r s)).lp) ∧
    (∀ r s : Fin t.nrows, (Sem.CertD.ruleOf t r.val s.val).fam < 5) ∧
    (∀ r s : Fin t.nrows, Consistent5 (Sem.CertD.ruleOf t r.val s.val).fam (patOf t r.val) (patOf t s.val)
      (rule5 (ri r s)).kp (rule5 (ri r s)).lp)
  eqs : ∀ g ∈ C.eqs, StiefelShape5 C g ∨ MargShape5 C g

variable {k d : ℕ}

open Stiefel in
/-- Stiefel identity, family `40` (`aaaa`), traced replica `0`. -/
theorem stiefel40_phys (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ) (hA : Aᴴ * A = (c : ℂ) • 1)
    (b : V1 k d → ℂ) : applyG (stF 0 ![1, 2, 3]) (Xf5 3 (vecOf A) b) = 0 :=
  applyG_stF_patVec so0 (famPat5 3) rfl A c hA b

open Marg Stiefel in
/-- `Tr_3 |aaab⟩⟨aaab| = Tr_3 |aaaa⟩⟨aaaa|` (survivors `0, 1, 2`) when `‖a‖ = ‖b‖`. -/
theorem aaa_phys (a b : V1 k d → ℂ) (hab : nsq k d a = nsq k d b) :
    applyG (fun _ => delK 3 ![0, 1, 2]) (Xf5 0 a b) = applyG (fun _ => delK 3 ![0, 1, 2]) (Xf5 3 a b) := by
  have e0 : applyG (fun l => delK (n := nf k d l) 3 ![0, 1, 2]) (Xf5 0 a b) =
      (∑ v, b v * star (b v)) • vecMulVec (w3 (famPat5 0 ∘ ![0, 1, 2]) a b)
        (star (w3 (famPat5 0 ∘ ![0, 1, 2]) a b)) :=
    applyG_delK_rank1 so3 (famPat5 0) a b
  have e3 : applyG (fun l => delK (n := nf k d l) 3 ![0, 1, 2]) (Xf5 3 a b) =
      (∑ v, a v * star (a v)) • vecMulVec (w3 (famPat5 3 ∘ ![0, 1, 2]) a b)
        (star (w3 (famPat5 3 ∘ ![0, 1, 2]) a b)) :=
    applyG_delK_rank1 so3 (famPat5 3) a b
  have hq : famPat5 0 ∘ ![0, 1, 2] = famPat5 3 ∘ ![0, 1, 2] := by decide
  rw [e0, e3, hq, ← nsq_eq a, ← nsq_eq b, hab]

open Marg Stiefel in
/-- `Tr_3 |bbba⟩⟨bbba| = Tr_3 |bbbb⟩⟨bbbb|` (survivors `0, 1, 2`) when `‖a‖ = ‖b‖`. -/
theorem bbb_phys (a b : V1 k d → ℂ) (hab : nsq k d a = nsq k d b) :
    applyG (fun _ => delK 3 ![0, 1, 2]) (Xf5 2 a b) = applyG (fun _ => delK 3 ![0, 1, 2]) (Xf5 4 a b) := by
  have e2 : applyG (fun l => delK (n := nf k d l) 3 ![0, 1, 2]) (Xf5 2 a b) =
      (∑ v, a v * star (a v)) • vecMulVec (w3 (famPat5 2 ∘ ![0, 1, 2]) a b)
        (star (w3 (famPat5 2 ∘ ![0, 1, 2]) a b)) :=
    applyG_delK_rank1 so3 (famPat5 2) a b
  have e4 : applyG (fun l => delK (n := nf k d l) 3 ![0, 1, 2]) (Xf5 4 a b) =
      (∑ v, b v * star (b v)) • vecMulVec (w3 (famPat5 4 ∘ ![0, 1, 2]) a b)
        (star (w3 (famPat5 4 ∘ ![0, 1, 2]) a b)) :=
    applyG_delK_rank1 so3 (famPat5 4) a b
  have hq : famPat5 2 ∘ ![0, 1, 2] = famPat5 4 ∘ ![0, 1, 2] := by decide
  rw [e2, e4, hq, ← nsq_eq a, ← nsq_eq b, hab]

end NPT.K4

#print axioms NPT.K4.stiefel40_phys
#print axioms NPT.K4.aaa_phys
#print axioms NPT.K4.bbb_phys
