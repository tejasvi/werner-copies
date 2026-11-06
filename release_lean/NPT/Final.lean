/-
NPT.Final — the discharged statements at the endpoint `t = 1/2` from the `d = 3` certificate: `EP_2` at
`d = 3` (restriction to two copies), `EP_3` at `d = 2` (zero padding), and the three-copy Werner theorem
at `d = 3`. The unconditional versions use the kernel-checked identity fact `NPT.Cert.EP3D3.idFact`; every theorem
here depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. The `*_of_idFact` versions take the
identity fact `hid` of the certificate as a hypothesis.
-/
import NPT.Main
import NPT.Copies
import NPT.Cert.EP3_d3

namespace NPT

/-- `EP_2` at `d = 3`: two qutrit copies. -/
theorem EP2_d3_of_idFact (hid : NPT.Cert.Sem.IdFact NPT.Cert.EP3D3.cert) : EP (Fin 2) 3 (1 / 2) :=
  EP2_of_EP3 (by norm_num) (NPT.Cert.EP3_d3_of_idFact hid)

/-- `EP_3` at `d = 2`: three qubit copies. -/
theorem EP3_d2_of_idFact (hid : NPT.Cert.Sem.IdFact NPT.Cert.EP3D3.cert) : EP (Fin 3) 2 (1 / 2) :=
  EP3_of_le (by norm_num) (NPT.Cert.EP3_d3_of_idFact hid)

/-- Paper, Theorem 1.1 at `d = 3` (Werner form) with the certificate discharged: given Costa Rico's
criterion, `ρ(3, α)` is 3-copy distillable iff `α < -1/2`. -/
theorem werner_three_copy_d3_of_idFact {D : ℕ → ℕ → ℝ → Prop} (hCR : CostaRico D)
    (hid : NPT.Cert.Sem.IdFact NPT.Cert.EP3D3.cert) {α : ℝ} (h0 : -1 ≤ α) (h1 : α ≤ 1) :
    D 3 3 α ↔ α < -1 / 2 :=
  werner_three_copy_d3 hCR (NPT.Cert.EP3_d3_of_idFact hid) h0 h1

/-- `EP_2` at `d = 3`: two qutrit copies (from `NPT.Cert.EP3_d3` by restriction). -/
theorem EP2_d3 : EP (Fin 2) 3 (1 / 2) := EP2_of_EP3 (by norm_num) NPT.Cert.EP3_d3

/-- `EP_3` at `d = 2`: three qubit copies (from `NPT.Cert.EP3_d3` by zero padding). -/
theorem EP3_d2 : EP (Fin 3) 2 (1 / 2) := EP3_of_le (by norm_num) NPT.Cert.EP3_d3

/-- Paper, Theorem 1.1 at `d = 3` (Werner form): given Costa Rico's criterion, `ρ(3, α)` is 3-copy distillable
iff `α < -1/2` (from `NPT.Cert.EP3_d3`). -/
theorem werner_three_copy_d3' {D : ℕ → ℕ → ℝ → Prop} (hCR : CostaRico D) {α : ℝ} (h0 : -1 ≤ α) (h1 : α ≤ 1) :
    D 3 3 α ↔ α < -1 / 2 :=
  werner_three_copy_d3 hCR NPT.Cert.EP3_d3 h0 h1

end NPT

#print axioms NPT.EP2_d3_of_idFact
#print axioms NPT.EP3_d2_of_idFact
#print axioms NPT.werner_three_copy_d3_of_idFact
#print axioms NPT.EP2_d3
#print axioms NPT.EP3_d2
#print axioms NPT.werner_three_copy_d3'
