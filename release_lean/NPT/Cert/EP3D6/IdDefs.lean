/-
NPT.Cert.EP3D6.IdDefs — tables and parameters of the d = 6 identity check (after the d = 3
`NPT.Cert.EP3D3.IdDefs`); see `NPT.Cert.EP3D6.IdFact`.
-/
import NPT.Cert.EP3D6.SemData
import NPT.Cert.EP3D6.GrpF
import NPT.Cert.Ident.Fast2
import NPT.Cert.Ident.Witness

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.EP3D6

/-- `Zq = zget · zmul + 2 · num` with `zmul = 2 Lden / 2^E` (`E = 182` for every block; checked in `grpOK`). -/
def zmul : ℕ := 2 * Lden / 2 ^ 182

/-- Objective tables: site factor `2 tr V_p − tr(V_21 V_p)` (n = 6), auxiliary factor `tr(V_21 V_p)` (n = 2). -/
def zsT (p : Fin 24) : ℤ := 2 * trF 6 p - trMulF 6 21 p
def zaT (p : Fin 24) : ℤ := trMulF 2 21 p

/-- Packing digit width (bits); `famCheck` checks the a-priori bound against it. -/
def bits : ℕ := 8300

/-- The parts of family `f` (rule groups `gs`, objective, equality entries), in the `Fast2` evaluation order
(`famPartsG2_eq`). -/
def partsN (f : ℕ) (gs : List GrpF) : List Part := famPartsG2 cert zmul f gs zsT zaT

end NPT.Cert.EP3D6
