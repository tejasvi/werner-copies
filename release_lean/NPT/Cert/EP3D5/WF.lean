/-
NPT.Cert.EP3D5.WF — well-formedness of the EP_3 d = 5 certificate (`NPT.Cert.EP3D5.cert`), checked by the kernel
(the d = 5 analogue of `NPT.Cert.WFd3`).
-/
import NPT.Cert.WFCheck
import NPT.Cert.EP3D5.SemData

namespace NPT.Cert.EP3D5

theorem wf_cert : NPT.Cert.wfCheck cert = true := by decide +kernel

end NPT.Cert.EP3D5

#print axioms NPT.Cert.EP3D5.wf_cert
