/-
NPT.Cert.Ident.KRRed — the reduced blocks of `ModP` computed by recursors:
`redRowsR p zmul b = redRows p zmul b`, so the mod-`p` certificate `certModR` used in kernel evaluation equals
`certMod`.
-/
import NPT.Cert.Ident.ModP
import NPT.Cert.Ident.KRLibEq

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident

namespace NPT.Cert.KR

theorem takePadR_eq {α : Type} (n : ℕ) (d : α) (l : List α) :
    takePadR n d l = (List.range n).map fun i => l.getD i d := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    cases l with
    | nil =>
      show d :: takePadR n d [] = _
      rw [ih]; simp [Function.comp_def]
    | cons a l =>
      show a :: takePadR n d l = _
      rw [ih]
      simp [Function.comp_def]

theorem zipWithR_eq {α β γ : Type} (f : α → β → γ) (l1 : List α) (l2 : List β) :
    zipWithR f l1 l2 = List.zipWith f l1 l2 := by
  induction l1 generalizing l2 with
  | nil => rfl
  | cons a l1 ih =>
    cases l2 with
    | nil => rfl
    | cons b l2 => show f a b :: zipWithR f l1 l2 = _; rw [ih]; rfl

theorem findR_eq {α : Type} (pred : α → Bool) (l : List α) : findR pred l = l.find? pred := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => Option α) (findR pred l) (some a) (pred a) = _
    rw [ih]
    cases h : pred a <;> simp [List.find?_cons, h]

theorem zipWith_range_map {β γ : Type} (f : ℕ → β → γ) (g : ℕ → β) (n : ℕ) :
    List.zipWith f (List.range n) ((List.range n).map g) = (List.range n).map fun i => f i (g i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.zipWith_append (by simp), ih]; simp

/-- Correction at `(a, c)` (first matching `uent` entry, either orientation). -/
noncomputable def corrR (uent : List (ℕ × ℕ × ℤ)) (a c : ℕ) : ℤ :=
  @Option.casesOn (ℕ × ℕ × ℤ) (fun _ => ℤ)
    (findR (fun e => orR (andR (Nat.beq e.1 a) (Nat.beq e.2.1 c)) (andR (Nat.beq e.1 c) (Nat.beq e.2.1 a))) uent)
    0 (fun e => Int.mul 2 e.2.2)

noncomputable def entryR (p zmul : ℕ) (uent : List (ℕ × ℕ × ℤ)) (a c : ℕ) (z : ℤ) : ℤ :=
  Int.emod (Int.add (Int.mul z (zmul : ℤ)) (corrR uent a c)) (p : ℤ)

/-- `entryR` evaluated without forming terms whose only big argument is a raw `zrows` literal: the stored entries are
multiples of `2^75`, so their hash (low 64 bits) is `0` and kernel caches would collide on them.  Every term built from
`z` first adds the position code `k = 65536 a + c + 1`. -/
noncomputable def entryR2 (p zmul : ℕ) (uent : List (ℕ × ℕ × ℤ)) (a c : ℕ) (z : ℤ) : ℤ :=
  Int.emod (Int.add (Int.sub (Int.mul (Int.emod (Int.add z (Int.ofNat (Nat.add (Nat.add (Nat.mul 65536 a) c) 1))) (p : ℤ))
      (Int.emod (zmul : ℤ) (p : ℤ)))
    (Int.mul (Int.ofNat (Nat.add (Nat.add (Nat.mul 65536 a) c) 1)) (Int.emod (zmul : ℤ) (p : ℤ)))) (corrR uent a c)) (p : ℤ)

theorem entryR2_eq (p zmul : ℕ) (uent : List (ℕ × ℕ × ℤ)) (a c : ℕ) (z : ℤ) :
    entryR2 p zmul uent a c z = entryR p zmul uent a c z := by
  unfold entryR2 entryR
  set k : ℤ := Int.ofNat (Nat.add (Nat.add (Nat.mul 65536 a) c) 1)
  show ((((z + k) % (p : ℤ)) * ((zmul : ℤ) % p) - k * ((zmul : ℤ) % p)) + corrR uent a c) % p =
    (z * zmul + corrR uent a c) % p
  have h1 : ((z + k) % (p : ℤ)) * ((zmul : ℤ) % p) - k * ((zmul : ℤ) % p) + corrR uent a c ≡
      (z + k) * zmul - k * zmul + corrR uent a c [ZMOD p] :=
    ((((Int.mod_modEq _ _).mul (Int.mod_modEq _ _)).sub ((Int.ModEq.refl k).mul (Int.mod_modEq _ _))).add
      (Int.ModEq.refl _))
  have h2 : (z + k) * zmul - k * zmul + corrR uent a c = z * zmul + corrR uent a c := by ring
  rw [h2] at h1
  exact h1

/-- Reduced `Zq` rows, by one pass over the stored rows. -/
noncomputable def redRowsR (p zmul : ℕ) (b : NPT.Cert.PBlock) : List (List ℤ) :=
  zipWithR (fun a row => zipWithR (fun c z => entryR2 p zmul b.uent a c z) (List.range b.n) (takePadR b.n 0 row))
    (List.range b.n) (takePadR b.n [] b.zrows)

theorem corrR_eq (b : NPT.Cert.PBlock) (a c : ℕ) :
    corrR b.uent a c = (match b.ufind a c with | some e => 2 * e.2.2 | none => 0) := by
  unfold corrR NPT.Cert.PBlock.ufind
  rw [findR_eq]
  have key : ∀ x y : ℕ, Nat.beq x y = (x == y) := fun x y => rfl
  have hp : (fun e : ℕ × ℕ × ℤ => orR (andR (Nat.beq e.1 a) (Nat.beq e.2.1 c)) (andR (Nat.beq e.1 c) (Nat.beq e.2.1 a))) =
      (fun e => (e.1 == a && e.2.1 == c) || (e.1 == c && e.2.1 == a)) := by
    funext e
    simp only [key]
    cases (e.1 == a) <;> cases (e.2.1 == c) <;> cases (e.1 == c) <;> cases (e.2.1 == a) <;> rfl
  rw [hp]
  cases b.uent.find? (fun e => (e.1 == a && e.2.1 == c) || (e.1 == c && e.2.1 == a)) <;> rfl

theorem redRowsR_eq (p zmul : ℕ) (b : NPT.Cert.PBlock) : redRowsR p zmul b = redRows p zmul b := by
  unfold redRowsR redRows
  rw [zipWithR_eq, takePadR_eq, zipWith_range_map]
  refine List.map_congr_left fun a _ => ?_
  rw [zipWithR_eq, takePadR_eq, zipWith_range_map]
  refine List.map_congr_left fun c _ => ?_
  rw [entryR2_eq]
  unfold entryR zqI NPT.Cert.PBlock.zget
  rw [corrR_eq]
  rfl

/-- The reduced block, by recursors. -/
noncomputable def redBlockR (p zmul : ℕ) (b : NPT.Cert.PBlock) : NPT.Cert.PBlock :=
  { b with zrows := redRowsR p zmul b, uent := [] }

/-- The mod-`p` certificate, by recursors (equal to `certMod`). -/
noncomputable def certModR (p zmul : ℕ) (C : CertD) : CertD :=
  { C with Z := mapR (redBlockR p zmul) C.Z, eqs := modEqs p C.eqs }

theorem certModR_eq (p zmul : ℕ) (C : CertD) : certModR p zmul C = certMod p zmul C := by
  unfold certModR certMod
  rw [mapR_eq]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  unfold redBlockR redBlock
  rw [redRowsR_eq]

end NPT.Cert.KR
