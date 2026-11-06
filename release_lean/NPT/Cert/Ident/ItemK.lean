/-
NPT.Cert.Ident.ItemK — kernel-cheap leaf tensors of rule-group items. `itemK` has the entries of `itemTF`, in the
same order (`itemK_eq`), but computes the multiplier rows `Zq` once per item and the rows `Y[ν] = Zq · W[s·nn+ν]` once
(mapped over the row list), stores the `W` rows sparsely (the `W` rows of the d = 3 certificate are 13–38% nonzero, so
zero terms are skipped instead of multiplied), nests the row lists by digits as consecutive groups (no index walks
per row or entry), and generates the entries `coef · ⟨W[r·nn+μ], Y[ν]⟩` directly in leaf order
`(μ0, ν0, μ1, ν1, μ2, ν2, μ3, ν3)` with an accumulator (no appends). `leafK` is the leaf sum (`leafK_eq`);
`ruleSpecK` is `ruleSpecT` with `leafK` (`ruleSpecK_eq`).
-/
import NPT.Cert.Ident.ItemF
import NPT.Cert.Ident.Fast

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

namespace IK

/-- Values `f (flat μ)` nested by the digits `μ0 < d0, …, μ3 < d3`. -/
def nestR {α : Type} (d0 d1 d2 d3 : ℕ) (f : ℕ → α) : List (List (List (List α))) :=
  (List.range d0).map fun a => (List.range d1).map fun b => (List.range d2).map fun c =>
    (List.range d3).map fun e => f (mr4 d0 d1 d2 d3 a b c e)

/-- `g x y` for `x ∈ xs` (outer) and `y ∈ ys` (inner), concatenated. -/
def pairs {α β γ : Type} (g : α → β → List γ) (xs : List α) (ys : List β) : List γ :=
  xs.flatMap fun x => ys.flatMap fun y => g x y

/-- `pairs` with an accumulator: `g x y acc` prepends the block of `(x, y)` to `acc` (no appends). -/
def pairsA {α β γ : Type} (g : α → β → List γ → List γ) (xs : List α) (ys : List β) (acc : List γ) : List γ :=
  xs.foldr (fun x acc => ys.foldr (fun y acc => g x y acc) acc) acc

/-- The first `n` entries of a list, padded with `dflt`. -/
def takeD {α : Type} (dflt : α) : ℕ → List α → List α
  | 0, _ => []
  | n + 1, [] => dflt :: takeD dflt n []
  | n + 1, x :: xs => x :: takeD dflt n xs

/-- `n` consecutive groups of `d` entries. -/
def grpN {α : Type} (d : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | n + 1, xs => xs.take d :: grpN d n (xs.drop d)

/-- A list over the flat index `mr4 μ0 μ1 μ2 μ3`, nested by the digits (consecutive groups). -/
def nestC {α : Type} (d0 d1 d2 d3 : ℕ) (L : List α) : List (List (List (List α))) :=
  grpN d1 d0 (grpN d2 (d0 * d1) (grpN d3 (d0 * d1 * d2) L))

/-- The nonzero entries of a row as pairs (number of zeros skipped before the entry, entry). -/
def sparseR : List Int → ℕ → List (ℕ × Int)
  | [], _ => []
  | a :: as, g => if a = 0 then sparseR as (g + 1) else (g, a) :: sparseR as 0

/-- `⟨u, v⟩` for a sparse row `u` (`sparseR`) and a dense row `v`. -/
def dotSp : List (ℕ × Int) → List Int → Int
  | (g, a) :: rest, ys => match ys.drop g with
    | y :: ys2 => a * y + dotSp rest ys2
    | [] => 0
  | [], _ => 0

/-- `⟨u, v⟩` for a dense row `u` and a sparse row `v` (`sparseR`). -/
def dotSpR : List Int → List (ℕ × Int) → Int
  | xs, (g, a) :: rest => match xs.drop g with
    | x :: xs2 => x * a + dotSpR xs2 rest
    | [] => 0
  | _, [] => 0

/-- Item tensor from the multiplier rows `Zq` and the row lists `Wr`, `Ws` (rows `r·nn + ·`, `s·nn + ·`), with
`Y[ν] = Zq · Ws[ν]`: the row lists are cut to `nn` rows, the `W` rows made sparse (zeros skipped) and nested by
digits, and the entries `coef · ⟨Wr[μ], Y[ν]⟩` generated in leaf order without appends. -/
def itemKc (Zq : List (List Int)) (coef : Int) (d0 d1 d2 d3 : ℕ) (Wr Ws : List (List Int)) : List SInt :=
  pairsA (pairsA (pairsA (pairsA fun sr yv acc => SInt.ofInt (coef * dotSp sr yv) :: acc)))
    (nestC d0 d1 d2 d3 ((takeD [] (d0 * d1 * d2 * d3) Wr).map fun wr => sparseR wr 0))
    (nestC d0 d1 d2 d3 ((takeD [] (d0 * d1 * d2 * d3) Ws).map fun ws =>
      let sw := sparseR ws 0
      Zq.map fun zrow => dotSpR zrow sw)) []

end IK

/-- Kernel-cheap leaf tensor of one item `(t, r, s)`; equal to `itemTF` (`itemK_eq`). -/
def itemK (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) : List SInt :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let nn := d0 * d1 * d2 * d3
  IK.itemKc ((List.range b.n).map fun a => (List.range b.n).map fun c => zqI b zmul a c) coef d0 d1 d2 d3
    (t.W.drop (it.2.1 * nn)) (t.W.drop (it.2.2 * nn))

/-- The leaf sum of a list of items. -/
def leafK (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ)) : List SInt :=
  (items.map (itemK C zmul coef d0 d1 d2 d3)).foldr addL []

/-- `ruleSpecT` with the leaf sums `leafK`. -/
def ruleSpecK (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (tab : List (List (List SInt))) : Spec where
  rows m := tab.getD m (localRowsF default kpos lpos)
  dimsq m := mdim C m * mdim C m
  leaf m1 m2 m3 lf := leafK C zmul coef (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3) lf.items

/-! ### Correctness -/

namespace IK

lemma dotI_eq_sum : ∀ (u v : List Int) (n : ℕ), (u.length ≤ n ∨ v.length ≤ n) →
    dotI u v = ∑ x ∈ range n, u.getD x 0 * v.getD x 0
  | [], v, n, _ => by simp [dotI]
  | a :: as, [], n, _ => by simp [dotI]
  | a :: as, b :: bs, n, h => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', dotI, dotI_eq_sum as bs m (by simp at h; omega)]
    simp [add_comm]

lemma range_mul_eq (d : ℕ) : ∀ n : ℕ,
    List.range (n * d) = (List.range n).flatMap fun a => (List.range d).map fun b => a * d + b
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, List.range_add, range_mul_eq d n, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

lemma flatMap_range_sq {γ : Type} (d : ℕ) (G : ℕ → List γ) :
    (List.range (d * d)).flatMap G = (List.range d).flatMap fun a => (List.range d).flatMap fun b => G (a * d + b) := by
  rw [range_mul_eq, List.flatMap_assoc]
  simp only [List.flatMap_map]

lemma map_range_sq {γ : Type} (d : ℕ) (G : ℕ → γ) :
    (List.range (d * d)).map G = (List.range d).flatMap fun a => (List.range d).map fun b => G (a * d + b) := by
  rw [List.map_eq_flatMap, flatMap_range_sq]
  simp only [← List.map_eq_flatMap]

lemma flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

lemma pairs_map {α β α' β' γ : Type} (g : α → β → List γ) (f1 : α' → α) (f2 : β' → β) (xs : List α')
    (ys : List β') : pairs g (xs.map f1) (ys.map f2) = xs.flatMap fun x => ys.flatMap fun y => g (f1 x) (f2 y) := by
  unfold pairs
  simp only [List.flatMap_map]

lemma foldr_flatMap {β γ : Type} (k : β → List γ → List γ) (h : β → List γ) (hk : ∀ y a, k y a = h y ++ a)
    (ys : List β) (A : List γ) : ys.foldr k A = ys.flatMap h ++ A := by
  induction ys with
  | nil => simp
  | cons y ys ih => rw [List.foldr_cons, ih, hk, List.flatMap_cons, List.append_assoc]

lemma pairsA_eq {α β γ : Type} (g : α → β → List γ → List γ) (h : α → β → List γ)
    (hg : ∀ x y acc, g x y acc = h x y ++ acc) (xs : List α) (ys : List β) (acc : List γ) :
    pairsA g xs ys acc = pairs h xs ys ++ acc :=
  foldr_flatMap _ _ (fun x a => foldr_flatMap _ _ (hg x) ys a) xs acc

lemma takeD_eq {α : Type} (dflt : α) : ∀ (n : ℕ) (L : List α),
    takeD dflt n L = (List.range n).map fun m => L.getD m dflt
  | 0, _ => rfl
  | n + 1, [] => by
    rw [takeD, takeD_eq dflt n [], List.range_succ_eq_map, List.map_cons, List.map_map]
    simp [Function.comp_def]
  | n + 1, x :: xs => by
    rw [takeD, takeD_eq dflt n xs, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp

lemma grpN_map_range {β : Type} (d : ℕ) : ∀ (n : ℕ) (f : ℕ → β),
    grpN d n ((List.range (n * d)).map f) = (List.range n).map fun j => (List.range d).map fun i => f (j * d + i)
  | 0, f => by simp [grpN]
  | n + 1, f => by
    have hsplit : (List.range ((n + 1) * d)).map f =
        (List.range d).map f ++ (List.range (n * d)).map (fun x => f (d + x)) := by
      rw [show (n + 1) * d = d + n * d by ring, List.range_add, List.map_append, List.map_map]
      rfl
    rw [grpN, hsplit, List.take_left' (by simp), List.drop_left' (by simp), grpN_map_range d n,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg₂ List.cons ?_ ?_
    · simp only [zero_mul, zero_add]
    · refine List.map_congr_left fun j _ => List.map_congr_left fun i _ => ?_
      congr 1
      simp only [Nat.succ_eq_add_one]
      ring

lemma nestC_eq {β : Type} (d0 d1 d2 d3 : ℕ) (f : ℕ → β) :
    nestC d0 d1 d2 d3 ((List.range (d0 * d1 * d2 * d3)).map f) = nestR d0 d1 d2 d3 f := by
  unfold nestC nestR
  rw [grpN_map_range d3 (d0 * d1 * d2) f, grpN_map_range d2 (d0 * d1), grpN_map_range d1 d0]
  rfl

lemma dotI_nil_right (u : List Int) : dotI u [] = 0 := by cases u <;> rfl

lemma dotSp_sparseR : ∀ (u : List Int) (g : ℕ) (v : List Int), dotSp (sparseR u g) v = dotI u (v.drop g)
  | [], g, v => by simp [sparseR, dotSp, dotI]
  | a :: as, g, v => by
    by_cases ha : a = 0
    · rw [sparseR, ite_eq_left ha, dotSp_sparseR as (g + 1) v, ha]
      rcases hv : v.drop g with _ | ⟨y, ys⟩
      · rw [show v.drop (g + 1) = [] by rw [← List.drop_drop, hv]; rfl, dotI_nil_right, dotI_nil_right]
      · rw [show v.drop (g + 1) = ys by rw [← List.drop_drop, hv]; rfl, dotI]
        ring
    · rw [sparseR, ite_eq_right ha]
      rcases hv : v.drop g with _ | ⟨y, ys⟩
      · simp [dotSp, hv, dotI_nil_right]
      · simp only [dotSp, hv, dotSp_sparseR as 0 ys, List.drop_zero, dotI]

lemma dotSpR_sparseR : ∀ (u : List Int) (g : ℕ) (v : List Int), dotSpR v (sparseR u g) = dotI (v.drop g) u
  | [], g, v => by simp [sparseR, dotSpR, dotI_nil_right]
  | a :: as, g, v => by
    by_cases ha : a = 0
    · rw [sparseR, ite_eq_left ha, dotSpR_sparseR as (g + 1) v, ha]
      rcases hv : v.drop g with _ | ⟨y, ys⟩
      · rw [show v.drop (g + 1) = [] by rw [← List.drop_drop, hv]; rfl]
        rfl
      · rw [show v.drop (g + 1) = ys by rw [← List.drop_drop, hv]; rfl, dotI]
        ring
    · rw [sparseR, ite_eq_right ha]
      rcases hv : v.drop g with _ | ⟨y, ys⟩
      · simp [dotSpR, hv, dotI]
      · simp only [dotSpR, hv, dotSpR_sparseR as 0 ys, List.drop_zero, dotI]

lemma itemKc_eq (Zq : List (List Int)) (coef : Int) (d0 d1 d2 d3 : ℕ) (Wr Ws : List (List Int)) :
    itemKc Zq coef d0 d1 d2 d3 Wr Ws =
      pairs (pairs (pairs (pairs fun wr yv => [SInt.ofInt (coef * dotI wr yv)])))
        (nestR d0 d1 d2 d3 fun m => Wr.getD m [])
        (nestR d0 d1 d2 d3 fun v => Zq.map fun zrow => dotI zrow (Ws.getD v [])) := by
  unfold itemKc
  rw [takeD_eq, takeD_eq, List.map_map, nestC_eq, List.map_map, nestC_eq]
  have h3 := pairsA_eq (fun sr yv acc => SInt.ofInt (coef * dotSp sr yv) :: acc)
    (fun sr yv => [SInt.ofInt (coef * dotSp sr yv)]) (fun _ _ _ => rfl)
  have h2 := pairsA_eq _ _ h3
  have h1 := pairsA_eq _ _ h2
  rw [pairsA_eq _ _ h1, List.append_nil]
  unfold nestR
  simp only [pairs_map, Function.comp_apply, dotSp_sparseR, dotSpR_sparseR, List.drop_zero]

lemma divmod_eq {a b d : ℕ} (hb : b < d) : (a * d + b) / d = a ∧ (a * d + b) % d = b := by
  have hd : 0 < d := by omega
  constructor
  · rw [add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hb, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

lemma getD_drop' {α : Type} (l : List α) (k m : ℕ) (d : α) : (l.drop k).getD m d = l.getD (k + m) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

end IK

open IK in
/-- **`itemK` is `itemTF`.** -/
theorem itemK_eq (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    itemK C zmul coef d0 d1 d2 d3 it = itemTF C zmul coef d0 d1 d2 d3 it := by
  -- the common nested form, with the entry function `F`
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let nn := d0 * d1 * d2 * d3
  let F : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → SInt := fun a0 b0 a1 b1 a2 b2 a3 b3 =>
    SInt.ofInt (coef * ∑ x ∈ range b.n, (t.W.getD (it.2.1 * nn + mr4 d0 d1 d2 d3 a0 a1 a2 a3) []).getD x 0 *
      ((itemY C zmul d0 d1 d2 d3 it).getD (mr4 d0 d1 d2 d3 b0 b1 b2 b3) []).getD x 0)
  have hTF : itemTF C zmul coef d0 d1 d2 d3 it =
      (List.range d0).flatMap fun a0 => (List.range d0).flatMap fun b0 =>
      (List.range d1).flatMap fun a1 => (List.range d1).flatMap fun b1 =>
      (List.range d2).flatMap fun a2 => (List.range d2).flatMap fun b2 =>
      (List.range d3).flatMap fun a3 => (List.range d3).map fun b3 => F a0 b0 a1 b1 a2 b2 a3 b3 := by
    unfold itemTF
    simp only [flatMap_range_sq, map_range_sq]
    refine flatMap_congr_mem fun a0 _ => flatMap_congr_mem fun b0 hb0 =>
      flatMap_congr_mem fun a1 _ => flatMap_congr_mem fun b1 hb1 =>
      flatMap_congr_mem fun a2 _ => flatMap_congr_mem fun b2 hb2 =>
      flatMap_congr_mem fun a3 _ => List.map_congr_left fun b3 hb3 => ?_
    obtain ⟨q0, r0⟩ := divmod_eq (a := a0) (List.mem_range.1 hb0)
    obtain ⟨q1, r1⟩ := divmod_eq (a := a1) (List.mem_range.1 hb1)
    obtain ⟨q2, r2⟩ := divmod_eq (a := a2) (List.mem_range.1 hb2)
    obtain ⟨q3, r3⟩ := divmod_eq (a := a3) (List.mem_range.1 hb3)
    simp only [itemE, q0, r0, q1, r1, q2, r2, q3, r3, F]
    rfl
  have hK : itemK C zmul coef d0 d1 d2 d3 it =
      (List.range d0).flatMap fun a0 => (List.range d0).flatMap fun b0 =>
      (List.range d1).flatMap fun a1 => (List.range d1).flatMap fun b1 =>
      (List.range d2).flatMap fun a2 => (List.range d2).flatMap fun b2 =>
      (List.range d3).flatMap fun a3 => (List.range d3).map fun b3 => F a0 b0 a1 b1 a2 b2 a3 b3 := by
    unfold itemK
    rw [itemKc_eq]
    unfold nestR
    simp only [pairs_map]
    simp only [← List.map_eq_flatMap]
    refine flatMap_congr_mem fun a0 _ => flatMap_congr_mem fun b0 hb0 =>
      flatMap_congr_mem fun a1 _ => flatMap_congr_mem fun b1 hb1 =>
      flatMap_congr_mem fun a2 _ => flatMap_congr_mem fun b2 hb2 =>
      flatMap_congr_mem fun a3 _ => List.map_congr_left fun b3 hb3 => ?_
    simp only [List.mem_range] at hb0 hb1 hb2 hb3
    have hν := mr4_lt d0 d1 d2 d3 b0 b1 b2 b3 hb0 hb1 hb2 hb3
    simp only [F, itemY]
    congr 2
    rw [getD_drop', getD_drop', List.map_map, getD_range_map _ _ _ _ hν,
      dotI_eq_sum _ _ b.n (Or.inr (by simp only [List.length_map, List.length_range]; exact le_rfl))]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    rw [getD_range_map _ _ _ _ hx', getD_range_map _ _ _ _ hx', Function.comp_apply,
      dotI_eq_sum _ _ b.n (Or.inl (by simp only [List.length_map, List.length_range]; exact le_rfl))]
    refine congrArg _ (Finset.sum_congr rfl fun c hc => ?_)
    rw [getD_range_map _ _ _ _ (Finset.mem_range.1 hc)]
  rw [hK, hTF]

theorem leafK_eq (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ)) :
    leafK C zmul coef d0 d1 d2 d3 items = (items.map (itemTF C zmul coef d0 d1 d2 d3)).foldr addL [] := by
  have h : itemK C zmul coef d0 d1 d2 d3 = itemTF C zmul coef d0 d1 d2 d3 := funext (itemK_eq C zmul coef d0 d1 d2 d3)
  rw [leafK, h]

theorem ruleSpecK_eq (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (tab : List (List (List SInt))) :
    ruleSpecK C zmul coef kpos lpos tab = ruleSpecT C zmul coef kpos lpos tab := by
  unfold ruleSpecK ruleSpecT
  congr 1
  funext m1 m2 m3 lf
  exact leafK_eq _ _ _ _ _ _ _ _

end NPT.Cert.Ident

#print axioms NPT.Cert.Ident.itemK_eq
#print axioms NPT.Cert.Ident.ruleSpecK_eq
