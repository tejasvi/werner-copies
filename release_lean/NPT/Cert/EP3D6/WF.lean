/-
NPT.Cert.EP3D6.WF — well-formedness of the EP_3 d = 6 certificate (`NPT.Cert.EP3D6.cert`), checked by the kernel
(the d = 6 analogue of `NPT.Cert.WFd3`).
-/
import NPT.Cert.WFCheck
import NPT.Cert.EP3D6.SemData

namespace NPT.Cert.EP3D6

theorem wf_cert : NPT.Cert.wfCheck cert = true := by decide +kernel

end NPT.Cert.EP3D6

#print axioms NPT.Cert.EP3D6.wf_cert
