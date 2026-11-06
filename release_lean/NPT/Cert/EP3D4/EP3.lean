/-
NPT.Cert.EP3D4.EP3 — the three-copy endpoint property at `d = 4`: `EP3D4.EP_of_idFact` (well-formedness and
PSD multipliers kernel-checked, standard axioms) applied to the kernel-checked identity fact `EP3D4.idFact`.
-/
import NPT.Cert.EP3D4.EP
import NPT.Cert.EP3D4.IdFact

namespace NPT.Cert

/-- **`EP_3` at `d = 4`.**

Kernel-checked throughout, standard axioms only: the identity fact `NPT.Cert.EP3D4.idFact` (class sums by mod-p
kernel checks and the Chinese remainder theorem, orbit witnesses, rule-group items; see its docstring), well-formedness
and the PSD multipliers (`EP3D4.EP_of_idFact`). -/
theorem EP3_d4 : NPT.EP (Fin 3) 4 (1 / 2) := EP3D4.EP_of_idFact EP3D4.idFact

end NPT.Cert

#print axioms NPT.Cert.EP3_d4
