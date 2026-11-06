/-
NPT.Cert.EP3D8.IdKChecks — rule-group item checks of the d = 8 identity fact by kernel evaluation (as
`NPT.Cert.EP3D3.IdKChecks`): every item of every rule group has the group's modules, rule and family
(`grpOK`), and the groups' items are a permutation of the family's multiplier entries (`itemsPerm`).
No `native_decide`.
-/
import NPT.Cert.EP3D8.IdDefs

open NPT.Cert.Ident NPT.Cert.Sem

namespace NPT.Cert.EP3D8

theorem grpOK_k_f0 : gs0.all (grpOK cert zmul) = true := by decide +kernel
theorem grpOK_k_f1 : gs1.all (grpOK cert zmul) = true := by decide +kernel
theorem grpOK_k_f2 : gs2.all (grpOK cert zmul) = true := by decide +kernel
theorem itemsPerm_k_f0 : (gs0.flatMap fun G => itemsOf G.tree).Perm (allItems cert 0) := by decide +kernel
theorem itemsPerm_k_f1 : (gs1.flatMap fun G => itemsOf G.tree).Perm (allItems cert 1) := by decide +kernel
theorem itemsPerm_k_f2 : (gs2.flatMap fun G => itemsOf G.tree).Perm (allItems cert 2) := by decide +kernel

end NPT.Cert.EP3D8
