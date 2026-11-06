/-
NPT.Cert.EP3D7.WF — well-formedness of the EP_3 d = 7 certificate (`NPT.Cert.EP3D7.cert`), checked by the kernel
(the d = 7 analogue of `NPT.Cert.WFd3`).
-/
import NPT.Cert.WFCheck
import NPT.Cert.EP3D7.SemData

namespace NPT.Cert.EP3D7

theorem wf_cert : NPT.Cert.wfCheck cert = true := by decide +kernel

end NPT.Cert.EP3D7

#print axioms NPT.Cert.EP3D7.wf_cert
