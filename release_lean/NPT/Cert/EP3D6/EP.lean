/-
NPT.Cert.EP3D6.EP — the three-copy endpoint property at `d = 6` from the d = 6 certificate
(`NPT.Cert.EP3D6.cert`): well-formedness (`wf_cert`, kernel), PSD multipliers (`blocks_psd`, kernel) and the
identity fact (`IdFact cert`) give `EP (Fin 3) 6 (1/2)` by `soundness_of_check` (as `NPT.Cert.EP3_d3` for d = 3).
-/
import NPT.Cert.EP3D6.WF

namespace NPT.Cert.EP3D6

instance : NeZero cert.d := ⟨by decide⟩

/-- `EP_3` at `d = 6`, from the identity fact of the d = 6 certificate. -/
theorem EP_of_idFact (hid : NPT.Cert.Sem.IdFact cert) : NPT.EP (Fin 3) 6 (1 / 2) :=
  NPT.Cert.soundness_of_check cert wf_cert hid blocks_psd

end NPT.Cert.EP3D6

#print axioms NPT.Cert.EP3D6.EP_of_idFact
