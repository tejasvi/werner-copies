/-
NPT.Cert.EP3D8.WF — well-formedness of the EP_3 d = 8 certificate (`NPT.Cert.EP3D8.cert`), checked by the kernel
(the d = 8 analogue of `NPT.Cert.WFd3`).
-/
import NPT.Cert.WFCheck
import NPT.Cert.EP3D8.SemData

namespace NPT.Cert.EP3D8

theorem wf_cert : NPT.Cert.wfCheck cert = true := by decide +kernel

end NPT.Cert.EP3D8

#print axioms NPT.Cert.EP3D8.wf_cert
