/-
NPT.Cert.EP3D5.EP — the three-copy endpoint property at `d = 5` from the d = 5 certificate
(`NPT.Cert.EP3D5.cert`): well-formedness (`wf_cert`, kernel), PSD multipliers (`blocks_psd`, kernel) and the
identity fact (`IdFact cert`) give `EP (Fin 3) 5 (1/2)` by `soundness_of_check` (as `NPT.Cert.EP3_d3` for d = 3).
-/
import NPT.Cert.EP3D5.WF

namespace NPT.Cert.EP3D5

instance : NeZero cert.d := ⟨by decide⟩

/-- `EP_3` at `d = 5`, from the identity fact of the d = 5 certificate. -/
theorem EP_of_idFact (hid : NPT.Cert.Sem.IdFact cert) : NPT.EP (Fin 3) 5 (1 / 2) :=
  NPT.Cert.soundness_of_check cert wf_cert hid blocks_psd

end NPT.Cert.EP3D5

#print axioms NPT.Cert.EP3D5.EP_of_idFact
