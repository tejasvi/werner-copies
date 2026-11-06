/-
NPT.K4.Keys4979 — the keys of the five-family (K4 @ 4979/10000) accumulator trees are the class representatives (kernel
checks): the leaves of `t0_<f>` carry the representatives `reps<f>` in order (`t0keys<f>`, f = 0..4), so every key of a
tree is a representative.
-/
import NPT.K4.Route.T4979.T0F0
import NPT.K4.Route.T4979.T0F1
import NPT.K4.Route.T4979.T0F2
import NPT.K4.Route.T4979.T0F3
import NPT.K4.Route.T4979.T0F4

open NPT.Cert.Ident NPT.K4.Route.T4979

namespace NPT.K4.D3T4979

theorem t0keys0 : t0_0.leaves.map Prod.fst = reps0 := by decide +kernel
theorem t0keys1 : t0_1.leaves.map Prod.fst = reps1 := by decide +kernel
theorem t0keys2 : t0_2.leaves.map Prod.fst = reps2 := by decide +kernel
theorem t0keys3 : t0_3.leaves.map Prod.fst = reps3 := by decide +kernel
theorem t0keys4 : t0_4.leaves.map Prod.fst = reps4 := by decide +kernel

end NPT.K4.D3T4979

#print axioms NPT.K4.D3T4979.t0keys1
#print axioms NPT.K4.D3T4979.t0keys4
