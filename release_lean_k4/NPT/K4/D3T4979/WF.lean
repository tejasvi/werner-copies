/- the five-family certificate (t = 4979/10000) is well formed in the sense of `NPT.K4.WF5` (the checker
`NPT.K4.wfCheck5`, kernel check). -/
import NPT.K4.D3T4979.SemData
import NPT.K4.WFCheck5

namespace NPT.K4.D3T4979

theorem wf5_cert : NPT.K4.wfCheck5 cert = true := by decide +kernel

end NPT.K4.D3T4979
