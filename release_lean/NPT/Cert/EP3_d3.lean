/-
NPT.Cert.EP3_d3 — the three-copy endpoint property at `d = 3` from the d = 3 certificate
(`NPT.Cert.EP3D3.cert`): well-formedness (`wf_cert`, kernel), PSD multipliers (`blocks_psd`,
kernel) and the identity fact (`IdFact cert`) give `EP (Fin 3) 3 (1/2)` by `soundness_of_check`.
-/
import NPT.Cert.WFd3
import NPT.Cert.EP3D3.IdFact

namespace NPT.Cert

instance : NeZero EP3D3.cert.d := ⟨by decide⟩

/-- `EP_3` at `d = 3`, from the identity fact of the d = 3 certificate. -/
theorem EP3_d3_of_idFact (hid : Sem.IdFact EP3D3.cert) : NPT.EP (Fin 3) 3 (1 / 2) :=
  soundness_of_check EP3D3.cert EP3D3.wf_cert hid EP3D3.blocks_psd

/-- **`EP_3` at `d = 3`** (the three-copy endpoint property for qutrits).

Fully kernel-checked: the identity fact `NPT.Cert.EP3D3.idFact` checks the class sums modulo pairwise-coprime moduli
by `decide +kernel` and concludes by the Chinese remainder theorem (see `NPT.Cert.EP3D3.IdFact` and
the package README); well-formedness, the PSD multipliers and soundness are kernel-checked as before.  No
`native_decide`: `#print axioms NPT.Cert.EP3_d3` lists only `propext`, `Classical.choice`, `Quot.sound`. -/
theorem EP3_d3 : NPT.EP (Fin 3) 3 (1 / 2) := EP3_d3_of_idFact EP3D3.idFact

end NPT.Cert

#print axioms NPT.Cert.EP3_d3_of_idFact
#print axioms NPT.Cert.EP3_d3
