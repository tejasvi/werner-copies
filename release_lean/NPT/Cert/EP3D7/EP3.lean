/-
NPT.Cert.EP3D7.EP3 — the three-copy endpoint property at `d = 7`: `EP3D7.EP_of_idFact` (well-formedness and
PSD multipliers kernel-checked, standard axioms) applied to the kernel-checked identity fact `EP3D7.idFact`.
-/
import NPT.Cert.EP3D7.EP
import NPT.Cert.EP3D7.IdFact

namespace NPT.Cert

/-- **`EP_3` at `d = 7`.**

Kernel-checked throughout, standard axioms only: the identity fact `NPT.Cert.EP3D7.idFact` (class sums by mod-p
kernel checks and the Chinese remainder theorem, orbit witnesses, rule-group items; see its docstring), well-formedness
and the PSD multipliers (`EP3D7.EP_of_idFact`). -/
theorem EP3_d7 : NPT.EP (Fin 3) 7 (1 / 2) := EP3D7.EP_of_idFact EP3D7.idFact

end NPT.Cert

#print axioms NPT.Cert.EP3_d7
