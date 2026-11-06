/-
NPT.K4.Keys497 — the keys of the K4@497 accumulator trees are the class representatives (kernel checks): the leaves
of `t0_<f>` carry the representatives `reps<f>` in order (`t0keys<f>`), so every key of a tree is a representative.
-/
import NPT.K4.Route.T497.T0F0
import NPT.K4.Route.T497.T0F1
import NPT.K4.Route.T497.T0F2

open NPT.Cert.Ident NPT.K4.Route.T497

namespace NPT.K4.D3T497

theorem t0keys0 : t0_0.leaves.map Prod.fst = reps0 := by decide +kernel
theorem t0keys1 : t0_1.leaves.map Prod.fst = reps1 := by decide +kernel
theorem t0keys2 : t0_2.leaves.map Prod.fst = reps2 := by decide +kernel

end NPT.K4.D3T497

#print axioms NPT.K4.D3T497.t0keys1
