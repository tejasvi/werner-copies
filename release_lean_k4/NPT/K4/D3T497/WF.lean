/-
NPT.K4.D3T497.WF — well-formedness of the K4 certificate at t = 497/1000 (`NPT.K4.D3T497.cert`, k = 4, d = 3): every
multiplier type uses verified entry rules consistent with its row patterns, every equality group has a Stiefel or
marginal shape (`NPT.Cert.wfCheck`), checked by the kernel.
-/
import NPT.Cert.WFCheck
import NPT.K4.D3T497.SemData

namespace NPT.K4.D3T497

theorem wf_cert : NPT.Cert.wfCheck cert = true := by decide +kernel

end NPT.K4.D3T497
