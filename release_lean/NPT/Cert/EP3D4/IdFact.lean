/-
NPT.Cert.EP3D4.IdFact — the identity fact `Sem.IdFact cert` of the EP_3 certificate at d = 4 (after
the d = 3 `IdFact`).

Kernel-checked throughout; no `native_decide`.  The class sums of every family vanish (`hsum_all`): the word values of
each family are packed and checked class by class modulo 6 pairwise-coprime 1200-bit moduli (`ps4`, packing width
1373) by `decide +kernel` (module `KChks` and its imports), and the Chinese remainder theorem with kernel-checked crude
word bounds (`KBound`, `KBoundP`) turns the congruences into equalities (`KHsum`):
* family 0: one declaration per modulus (`KChk<i>_0`; `KR.hsum_of_checksB` via `KAssembly`);
* family 1: each check split over 2 declarations (rule groups 5–7 | 8–11, the last with the other parts) whose class
  trees start at offsets that cancel mod p (`KChkS<i>_1_<j>`, offsets `KOff<i>_1`;
  `KR.hsum_of_checks_split` with `KRSplitAsm.hsplit_last`, via `KAssemblyS`);
* family 2: one declaration per modulus (`KChk<i>_2`; `KR.hsum_of_checksB` via `KAssembly`).
The orbit witnesses of all words are kernel-checked (`NPT.Cert.EP3D3.witCheckK_f*`, module `EP3D3.WitK`;
the orbits are the same for every d), as are the rule-group items and their cover (`IdKChecks`), the row and
equality tables (`KTabT`, `KEqT<i>`) and the class-list lengths (`EP3D3.KClsLen`).  The earlier version
with three `native_decide` class-sum checks is kept as `IdFactNative.lean` (not imported).
-/
import NPT.Cert.EP3D4.KHsum
import NPT.Cert.EP3D4.KChks
import NPT.Cert.EP3D3.WitK

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.EP3D4

/-- Class data by family (the d = 3 orbits). -/
def clsL (f : ℕ) : List ℕ := if f = 0 then EP3D3.cls0 else if f = 1 then EP3D3.cls1 else EP3D3.cls2
def witL (f : ℕ) : List ℕ := if f = 0 then EP3D3.wit0 else if f = 1 then EP3D3.wit1 else EP3D3.wit2

lemma witCheck_all (f : ℕ) (hf : f < 3) : witCheck f (clsL f) (witL f) = true := by
  interval_cases f
  · exact EP3D3.witCheckK_f0
  · exact EP3D3.witCheckK_f1
  · exact EP3D3.witCheckK_f2

lemma hsum_all (f : ℕ) (hf : f < 3) (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => (clsL f).getD (posW w) 0 = (clsL f).getD (posW w₀) 0),
      cert.Λ f w = 0 := by
  interval_cases f
  · exact hsumC_f0 chks_f0 w₀
  · exact hsumC_f1 chks_f1 w₀
  · exact hsumC_f2 chks_f2 w₀

/-- **The identity fact of the d = 4 certificate** (kernel-checked, see the module docstring). -/
def idFact : IdFact cert where
  cls f w := (clsL f).getD (posW w) 0
  rep _ c := wordOfCode c
  wit f w := decWit ((witL f).getD (posW w) 0)
  hG f hf w := ⟨(witCheck_fields f (clsL f) (witL f) (witCheck_all f hf) w).1,
    (witCheck_fields f (clsL f) (witL f) (witCheck_all f hf) w).2.1⟩
  hσ _ _ _ := decWit_bij _
  hrep f hf w := (witCheck_fields f (clsL f) (witL f) (witCheck_all f hf) w).2.2
  hsum f hf w₀ := hsum_all f hf w₀

end NPT.Cert.EP3D4

#print axioms NPT.Cert.EP3D4.idFact
