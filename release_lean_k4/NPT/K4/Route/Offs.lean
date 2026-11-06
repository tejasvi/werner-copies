/-
NPT.K4.Route.Offs — accumulators with offsets: the offsets `(key, value)` are added to the leaves of a fixed tree.
-/
import NPT.Cert.Ident.Core

namespace NPT.K4.Route

open NPT.Cert.Ident

/-- The tree `t` with each offset `(k, v)` added to the leaf of key `k`. -/
def tOff (t : AT) (offs : List (Nat × Int)) : AT := offs.foldl (fun t e => t.add e.1 (SInt.ofInt e.2)) t

/-- Offsets from integer rows `[key, value]`. -/
def offsOfRows (rows : List (List Int)) : List (Nat × Int) := rows.map fun r => ((r.getD 0 0).toNat, r.getD 1 0)

/-- The residual of class `j` from a list of values in the order of `reps` (as `NPT.K4.RintOf`). -/
def RintOfR (reps : List Nat) (vals : List Int) (j : Nat) : Int := if j ∈ reps then vals.getD (reps.idxOf j) 0 else 0

end NPT.K4.Route
