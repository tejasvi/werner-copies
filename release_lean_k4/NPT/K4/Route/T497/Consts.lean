/-
NPT.K4.Route.T497.Consts — the constants of the K4 @ 497/1000 slice checks: digit width, block exponent and the part
coefficients for `D = 2^224 · 1000^4 · 162^4` (`cG · 2^224 = −D`, `cO = D/(1000^4·162^4)`, `cT = −D·nu/162^4` with
`nu = nuNum/2^94`, `cE = D/2^90`).
-/
import NPT.K4.D3T497.Common

namespace NPT.K4.Route.T497

/-- Packing digit width (bits); every slice check verifies its a-priori bound against it. -/
def bP : ℕ := 320
/-- Exponent of every block (`Z_t = Zs_t / 2^224`; checked in `grpOK5`). -/
def E0 : ℕ := 224
def cG : ℤ := -(1000 ^ 4 * (2 * 3 ^ 4) ^ 4)
def cO : ℤ := 2 ^ 224
def cT : ℤ := -(2 ^ 130 * 1000 ^ 4 * (NPT.K4.D3T497.nuNum : ℤ))
def cE : ℤ := 2 ^ 134 * 1000 ^ 4 * (2 * 3 ^ 4) ^ 4

end NPT.K4.Route.T497
