/-
NPT.Cert.EP3D3.IdFact — the identity fact `Sem.IdFact cert` of the EP_3 certificate at d = 3.

Kernel-checked throughout; no `native_decide`.  The class sums of every family vanish (`hsum_all`): the word values of
each family are packed and checked class by class modulo pairwise-coprime moduli by `decide +kernel` (module `KChks`
and its imports), and the Chinese remainder theorem with kernel-checked crude word bounds (`KBound`, `KBoundW`)
turns the congruences into equalities:
* family 2: ten 600-bit moduli, packing width 760, one declaration per modulus (`KChk<i>_2`; `KR.hsum_of_checks`
  via `KAssembly`, `KHsum`);
* family 0: five 1200-bit moduli, width 1360, equality parts as one λ-box per part (`KChkW<i>_0`;
  `KR.hsum_of_checksB`);
* family 1: the same five moduli, each check split over two declarations (rule groups 5–7, and 8–11 with the other
  parts) whose class trees start at offsets that cancel mod p (`KChkS<i>_1_<j>`, offsets `KOff1_<i>`;
  `KR.hsum_of_checks_split` with `hsplit_last`, via `KAssemblyS`).
The orbit witnesses of all words are kernel-checked as before (`witCheckK_f*`, module `WitK`), as are the
rule-group items and their cover (`IdKChecks`), the row and equality tables (`KTabT<g>`, `KEqT<i>`) and the class
lists' lengths (`KClsLen`).  The earlier version with three `native_decide` class-sum checks is kept as
`IdFactNative.lean` (not imported).
-/
import NPT.Cert.EP3D3.KHsum
import NPT.Cert.EP3D3.KChks
import NPT.Cert.EP3D3.ClassL
import NPT.Cert.EP3D3.WitK

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.EP3D3

lemma witCheck_all (f : ℕ) (hf : f < 3) : witCheck f (clsL f) (witL f) = true := by
  interval_cases f
  · exact witCheckK_f0
  · exact witCheckK_f1
  · exact witCheckK_f2

lemma hsum_all (f : ℕ) (hf : f < 3) (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => (clsL f).getD (posW w) 0 = (clsL f).getD (posW w₀) 0),
      cert.Λ f w = 0 := by
  interval_cases f
  · exact hsumC_f0 chks_f0 w₀
  · exact hsumS_f1_done w₀
  · exact hsumC_f2 chks_f2 w₀

/-- **The identity fact of the d = 3 certificate** (kernel-checked, see the module docstring). -/
def idFact : IdFact cert where
  cls f w := (clsL f).getD (posW w) 0
  rep _ c := wordOfCode c
  wit f w := decWit ((witL f).getD (posW w) 0)
  hG f hf w := ⟨(witCheck_fields f (clsL f) (witL f) (witCheck_all f hf) w).1,
    (witCheck_fields f (clsL f) (witL f) (witCheck_all f hf) w).2.1⟩
  hσ _ _ _ := decWit_bij _
  hrep f hf w := (witCheck_fields f (clsL f) (witL f) (witCheck_all f hf) w).2.2
  hsum f hf w₀ := hsum_all f hf w₀

end NPT.Cert.EP3D3
