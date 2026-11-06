/-
NPT.Cert.EP3D4.WF — well-formedness of the EP_3 d = 4 certificate (`NPT.Cert.EP3D4.cert`), checked by the kernel
(the d = 4 analogue of `NPT.Cert.WFd3`).
-/
import NPT.Cert.WFCheck
import NPT.Cert.EP3D4.SemData

namespace NPT.Cert.EP3D4

theorem wf_cert : NPT.Cert.wfCheck cert = true := by decide +kernel

end NPT.Cert.EP3D4

#print axioms NPT.Cert.EP3D4.wf_cert
