/-
NPT.Cert.WFd3 — well-formedness of the EP_3 d = 3 certificate (`NPT.Cert.EP3D3.cert`), checked by the kernel.
-/
import NPT.Cert.WFCheck
import NPT.Cert.EP3D3.SemData

namespace NPT.Cert.EP3D3

theorem wf_cert : NPT.Cert.wfCheck cert = true := by decide +kernel

end NPT.Cert.EP3D3

#print axioms NPT.Cert.EP3D3.wf_cert
