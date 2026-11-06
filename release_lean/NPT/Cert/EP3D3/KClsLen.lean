/-
NPT.Cert.EP3D3.KClsLen — lengths of the class lists (kernel), for `hsum_of_checks`.
-/
import NPT.Cert.EP3D3.Class0
import NPT.Cert.EP3D3.Class1
import NPT.Cert.EP3D3.Class2
set_option maxRecDepth 1000000

namespace NPT.Cert.EP3D3
open NPT.Cert.Ident

theorem cls0_len : cls0.length = 24 * slen := by decide +kernel
theorem cls1_len : cls1.length = 24 * slen := by decide +kernel
theorem cls2_len : cls2.length = 24 * slen := by decide +kernel

end NPT.Cert.EP3D3
