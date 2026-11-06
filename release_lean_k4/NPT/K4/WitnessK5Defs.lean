/-
NPT.K4.WitnessK5Defs — the kernel-evaluable orbit-witness check for five legs: the per-word check `witOKK5`
(packed tables, kernel-accelerated `Nat` operations only) and the list check `witGoK5` (with the end position). The
tables `MT`, `ET`, `GT` and `digQ` are the k = 3 ones (`NPT.Cert.Ident.WitnessKDefs`); `ST5` is the source leg of `act`
for the 24 site permutations. Soundness: `NPT.K4.WitnessK5`.
-/
import NPT.Cert.Ident.WitnessKDefs

namespace NPT.K4

open NPT.Cert.Ident

/-- Entry `(si, l)` at bit `3 (5 si + l)`: the source leg of `act` for `σ = s4F si` (`σ⁻¹ l` for `l < 4`, `4` for
`l = 4`). -/
def ST5 : Nat :=
  1180256087293518280651974652083382816915955172431922937730229540675623726921203230803308521334307822208566920

def srcT5 (si l : Nat) : Nat := Nat.land (Nat.shiftRight ST5 (Nat.mul 3 (Nat.add (Nat.mul 5 si) l))) 7

/-- Leg `l` of the acted word (`act` with `σ = s4F si`, inversion iff `e = 1`). -/
def newL5 (q g1 g2 si e l : Nat) : Nat := invE e (mulT g1 (mulT (digQ q (srcT5 si l)) g2))

/-- Kernel check of the word at position `q` with class code `c` (a position) and witness code `wc`. -/
def witOKK5 (f q c wc : Nat) : Bool :=
  let e := Nat.mod wc 2
  let si := Nat.mod (Nat.div wc 2) 24
  let g2 := Nat.mod (Nat.div wc 48) 24
  let g1 := Nat.mod (Nat.div wc 1152) 24
  gmB f g1 && gmB f g2 &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (newL5 q g1 g2 si e 4) 331776)
      (Nat.mul (newL5 q g1 g2 si e 3) 13824)) (Nat.mul (newL5 q g1 g2 si e 2) 576))
      (Nat.mul (newL5 q g1 g2 si e 1) 24)) (newL5 q g1 g2 si e 0)) c

/-- Check positions `q, q + 1, …` and that the lists end together at position `stop`. -/
def witGoK5 (f stop : Nat) : Nat → List Nat → List Nat → Bool
  | q, c :: cs, wc :: ws => witOKK5 f q c wc && witGoK5 f stop (Nat.succ q) cs ws
  | q, [], [] => Nat.beq q stop
  | _, _, _ => false

end NPT.K4
