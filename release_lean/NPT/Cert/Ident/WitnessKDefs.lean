/-
NPT.Cert.Ident.WitnessKDefs — the kernel-evaluable orbit-witness check: packed tables and the per-word
check `witOKK`, using only kernel-accelerated `Nat` operations and no branching on `Decidable` instances, and the
list checks `witGoK` (with the end position, so lengths are checked too) and `stripsR` (decomposition into slices). No imports beyond the core
library, so that the kernel chunk checks load little. Soundness: `NPT.Cert.Ident.WitnessK`.
-/

namespace NPT.Cert.Ident

/-- `mulIdx p q` (`p q < 24`) at bit `5 (24 p + q)`. -/
def MT : Nat := 963083904067687740382735603551689858979262908457194405886049381333969802301183085837553985273473854330919290650503943115840069356509638955686872359685717332808901270679562285084298514669757260143135839602817718328491187159082064147838148221860841857298935111617501776737072422980980029411854874636928447370107983835290263782952548816511020583812907530610125653564010220842482491962004376120388759761678501504925865068116183498263901531782434546190694459208408295563000458219589420019657733870239199217371120552283113993841669272690250937181101628696532967492507089921218779169242377132803342235395010373055173633197438399586503732527643592394751693744750901567759454225611815304897823538575145718919194832468029427789693900593094299686717877973378999991997074262632222442029776699593767455265065230686956072508893019315770005973264241629444791670033435835305658400

/-- Entry `(e, x)` at bit `5 (24 e + x)`: `x` for `e = 0`, `pinvIdx x` for `e = 1`. -/
def ET : Nat := 1300411937678511808125138077326825464258675421103280647002365882441762848

/-- Entry `(si, l)` at bit `2 (4 si + l)`: the source factor of `act` for `σ = s3F si` (`σ⁻¹ l` for `l < 3`,
`3` for `l = 3`). -/
def ST : Nat := 218570128742628

/-- Bit `24 f + g` is `inG f g` (`f < 3`; `G_0 = G_2` fix replica 3, `G_1` preserves `{0, 1}`). -/
def GT : Nat := 5856086893736776005

def mulT (p q : Nat) : Nat := Nat.land (Nat.shiftRight MT (Nat.mul 5 (Nat.add (Nat.mul 24 p) q))) 31

def invE (e x : Nat) : Nat := Nat.land (Nat.shiftRight ET (Nat.mul 5 (Nat.add (Nat.mul 24 e) x))) 31

def srcT (si l : Nat) : Nat := Nat.land (Nat.shiftRight ST (Nat.mul 2 (Nat.add (Nat.mul 4 si) l))) 3

def gmB (f g : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight GT (Nat.add (Nat.mul 24 f) g)) 1) 1

/-- Digit `s` of a position (`wordAt q s`). -/
def digQ (q s : Nat) : Nat := Nat.mod (Nat.div q (Nat.pow 24 s)) 24

/-- Factor `l` of the acted word (`act` with `σ = s3F si`, inversion iff `e = 1`). -/
def newL (q g1 g2 si e l : Nat) : Nat := invE e (mulT g1 (mulT (digQ q (srcT si l)) g2))

/-- Kernel check of the word at position `q` with class code `c` and witness code `wc` (fields as in `decWit`). -/
def witOKK (f q c wc : Nat) : Bool :=
  let e := Nat.mod wc 2
  let si := Nat.mod (Nat.div wc 2) 6
  let g2 := Nat.mod (Nat.div wc 12) 24
  let g1 := Nat.mod (Nat.div wc 288) 24
  gmB f g1 && gmB f g2 &&
    Nat.beq (Nat.add (Nat.add (Nat.add (Nat.mul (newL q g1 g2 si e 0) 13824) (Nat.mul (newL q g1 g2 si e 1) 576))
      (Nat.mul (newL q g1 g2 si e 2) 24)) (newL q g1 g2 si e 3)) c

/-- Check positions `q, q + 1, …` and that the lists end together at position `stop`. -/
def witGoK (f stop : Nat) : Nat → List Nat → List Nat → Bool
  | q, c :: cs, wc :: ws => witOKK f q c wc && witGoK f stop (Nat.succ q) cs ws
  | q, [], [] => Nat.beq q stop
  | _, _, _ => false

/-- `stripR s l = some r` iff `l = s ++ r`. Written with the recursor (few terms per step in the kernel). -/
noncomputable def stripR (s : List Nat) : List Nat → Option (List Nat) :=
  @List.rec Nat (fun _ => List Nat → Option (List Nat)) (fun l => some l)
    (fun b _ ih l => @List.casesOn Nat (fun _ => Option (List Nat)) l none fun a as => cond (Nat.beq a b) (ih as) none) s

/-- `stripsR ss l = true` iff `l = ss.flatten`. -/
noncomputable def stripsR (ss : List (List Nat)) : List Nat → Bool :=
  @List.rec (List Nat) (fun _ => List Nat → Bool) (fun l => l.isEmpty)
    (fun s _ ih l => @Option.casesOn (List Nat) (fun _ => Bool) (stripR s l) false ih) ss

end NPT.Cert.Ident
