/-
NPT.K4.Route.T4979.Consts — the constants of the K4 @ 4979/10000 (five families) slice checks: digit width, block exponent and
the part coefficients for `D = 2^254 · 10000^4 · 162^4` (`cG · 2^254 = −D`, `cO = D/(10000^4·162^4)`, `cT = −D·nu/162^4`
with `nu = nuNum/2^99`, `cE = D/2^120`).
-/
import NPT.K4.D3T4979.Common

namespace NPT.K4.Route.T4979

/-- Packing digit width (bits); every slice check verifies its a-priori bound against it (provisional, to be set from
the phase-1 maxima). -/
def bP : ℕ := 400
/-- Exponent of every block (`Z_t = Zs_t / 2^254`; checked in `grpOK5`). -/
def E0 : ℕ := 254
def cG : ℤ := -(10000 ^ 4 * (2 * 3 ^ 4) ^ 4)
def cO : ℤ := 2 ^ 254
def cT : ℤ := -(2 ^ 155 * 10000 ^ 4 * (NPT.K4.D3T4979.nuNum : ℤ))
def cE : ℤ := 2 ^ 134 * 10000 ^ 4 * (2 * 3 ^ 4) ^ 4

end NPT.K4.Route.T4979
