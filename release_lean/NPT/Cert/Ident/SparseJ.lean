/-
NPT.Cert.Ident.SparseJ — local rows and `del` entries from the nonzero rows of `J` (for the d = 4..8 kernel
identity facts).  The certificates' `J` are 0/±1 with few nonzero rows (at most 120 of `n^4 ≤ 4096` at d ≤ 8), but the
kernel reads `J.getD x` by walking the list, so `mkTab`/`mkTabG` (all `n^4` support pairs) and `eqTabOf` (`n^4`
terms per entry) are out of reach at n ≥ 4.  Here:
* `spRows N J`: the nonzero rows `(index, row)` of `J` with index `< N`; `sum_spRows`: a sum over `range N` whose
  terms vanish on zero rows is a sum over `spRows N J`;
* `localRowsF_sp`, `mkTab_sp`: local rows from pairs of nonzero rows, the entry-rule condition split into x-only,
  y-only and keyed mixed edges (`condE_split`), evaluated as a filtered join (`pairsE`);
* `delFast_sp`, `eqTabOf_sp`: `delFast` over the nonzero rows `u` of the 3-replica `J` and the traced digit `z`, the
  second row looked up among the nonzero rows.
-/
import NPT.Cert.Ident.Fast2
import NPT.Cert.Ident.ChunkSpec

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-! ### Nonzero rows -/

/-- The nonzero rows `(i + k, rs[k])` of `rs` with `i + k < N`. -/
def spRowsAux (N : ℕ) : ℕ → List (List Int) → List (ℕ × List Int)
  | _, [] => []
  | i, r :: rs => if i < N ∧ r.any (· != 0) = true then (i, r) :: spRowsAux N (i + 1) rs else spRowsAux N (i + 1) rs

/-- The nonzero rows of `J` with index `< N`, as `(index, row)`. -/
def spRows (N : ℕ) (J : List (List Int)) : List (ℕ × List Int) := spRowsAux N 0 J

lemma getD_zero_of_any {r : List Int} (h : ¬ r.any (· != 0) = true) (μ : ℕ) : r.getD μ 0 = 0 := by
  have h' : ∀ x ∈ r, x = 0 := by
    intro x hx
    by_contra hne
    exact h (List.any_eq_true.2 ⟨x, hx, by simpa using hne⟩)
  rcases Nat.lt_or_ge μ r.length with hμ | hμ
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hμ, Option.getD_some]
    exact h' _ (List.getElem_mem hμ)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hμ, Option.getD_none]

lemma sum_spRowsAux (N : ℕ) (F : ℕ → List Int → ℤ) (hF : ∀ x r, (∀ μ, r.getD μ 0 = 0) → F x r = 0) :
    ∀ (rs : List (List Int)) (i : ℕ), ((spRowsAux N i rs).map fun a => F a.1 a.2).sum =
      ∑ k ∈ range rs.length, if i + k < N then F (i + k) (rs.getD k []) else 0
  | [], i => by simp [spRowsAux]
  | r :: rs, i => by
    have ih' : ((spRowsAux N (i + 1) rs).map fun a => F a.1 a.2).sum =
        ∑ k ∈ range rs.length, if i + (k + 1) < N then F (i + (k + 1)) (rs.getD k []) else 0 := by
      rw [sum_spRowsAux N F hF rs (i + 1)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show i + 1 + k = i + (k + 1) by omega]
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    rw [← ih']
    simp only [spRowsAux]
    by_cases hi : i < N
    · by_cases hr : r.any (· != 0) = true
      · rw [ite_eq_left ⟨hi, hr⟩, List.map_cons, List.sum_cons, ite_eq_left hi]; ring
      · rw [ite_eq_right (fun h => hr h.2), ite_eq_left hi, hF i r (getD_zero_of_any hr)]; ring
    · rw [ite_eq_right (fun h => hi h.1), ite_eq_right hi]; ring

/-- **Sums over the nonzero rows.** -/
theorem sum_spRows (N : ℕ) (J : List (List Int)) (F : ℕ → List Int → ℤ)
    (hF : ∀ x r, (∀ μ, r.getD μ 0 = 0) → F x r = 0) :
    ((spRows N J).map fun a => F a.1 a.2).sum = ∑ x ∈ range N, F x (J.getD x []) := by
  rw [spRows, sum_spRowsAux N F hF J 0]
  simp only [Nat.zero_add]
  rw [← Finset.sum_filter]
  have hfil : (range J.length).filter (fun k => k < N) = range (min J.length N) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfil]
  apply Finset.sum_subset
  · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
  · intro x hx hx'
    simp only [Finset.mem_range] at hx hx'
    apply hF
    intro μ
    have hJ : J.length ≤ x := by omega
    have h0 : J.getD x [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hJ, Option.getD_none]
    rw [h0]
    simp

/-! ### Local rows -/

/-- `kmatF` over pairs of nonzero rows. -/
lemma kmatF_sp (n : ℕ) (J : List (List Int)) (kpos lpos : List ℕ) (p : Fin 24) (μ ν : ℕ) :
    kmatF n J kpos lpos p μ ν = ((spRows (n ^ 4) J).map fun a => ((spRows (n ^ 4) J).map fun b =>
      if condF n kpos lpos p a.1 b.1 then a.2.getD μ 0 * b.2.getD ν 0 else 0).sum).sum := by
  set S := spRows (n ^ 4) J
  let Fo : ℕ → List Int → ℤ := fun x r => (S.map fun b =>
    if condF n kpos lpos p x b.1 then r.getD μ 0 * b.2.getD ν 0 else 0).sum
  have hFo : ∀ x r, (∀ μ, r.getD μ 0 = 0) → Fo x r = 0 := by
    intro x r hr
    simp only [Fo, hr, zero_mul, ite_self, List.map_const', List.sum_replicate, smul_zero]
  calc kmatF n J kpos lpos p μ ν = ∑ xi ∈ range (n ^ 4), Fo xi (J.getD xi []) := by
        unfold kmatF
        refine Finset.sum_congr rfl fun xi _ => ?_
        let Fi : ℕ → List Int → ℤ := fun y r =>
          if condF n kpos lpos p xi y then (J.getD xi []).getD μ 0 * r.getD ν 0 else 0
        have hFi : ∀ y r, (∀ μ, r.getD μ 0 = 0) → Fi y r = 0 := by
          intro y r hr; simp only [Fi, hr, mul_zero, ite_self]
        rw [show Fo xi (J.getD xi []) = (S.map fun b => Fi b.1 b.2).sum from rfl, sum_spRows _ _ Fi hFi]
        refine Finset.sum_congr rfl fun yi _ => ?_
        simp only [Fi]
        split_ifs <;> ring
    _ = (S.map fun a => Fo a.1 a.2).sum := (sum_spRows _ _ Fo hFo).symm

/-- Edge classes of an edge list on the 8 digit positions (`< 4`: digits of `x`, the others: digits of `y`). -/
def xxE (E : List (ℕ × ℕ)) : List (ℕ × ℕ) := E.filter fun e => decide (e.1 < 4) && decide (e.2 < 4)
def yyE (E : List (ℕ × ℕ)) : List (ℕ × ℕ) := E.filter fun e => !decide (e.1 < 4) && !decide (e.2 < 4)
def xyE (E : List (ℕ × ℕ)) : List (ℕ × ℕ) := E.filter fun e => decide (e.1 < 4) != decide (e.2 < 4)
/-- The `x` end and the `y` end (as a digit of `y`) of a mixed edge. -/
def xEnd (e : ℕ × ℕ) : ℕ := if e.1 < 4 then e.1 else e.2
def yEnd (e : ℕ × ℕ) : ℕ := if e.1 < 4 then e.2 - 4 else e.1 - 4

/-- The x-only edges hold. -/
def okX (n : ℕ) (E : List (ℕ × ℕ)) (x : ℕ) : Bool := (xxE E).all fun e => dgt n 4 x e.1 == dgt n 4 x e.2
/-- The y-only edges hold. -/
def okY (n : ℕ) (E : List (ℕ × ℕ)) (y : ℕ) : Bool :=
  (yyE E).all fun e => dgt n 4 y (e.1 - 4) == dgt n 4 y (e.2 - 4)
/-- Base-16 code of a digit list. -/
def enc16 (l : List ℕ) : ℕ := l.foldr (fun d acc => d + 16 * acc) 0
/-- Keys of the mixed edges: the mixed edges hold iff `keyX x = keyY y` (digits `< 16`). -/
def keyX (n : ℕ) (E : List (ℕ × ℕ)) (x : ℕ) : ℕ := enc16 ((xyE E).map fun e => dgt n 4 x (xEnd e))
def keyY (n : ℕ) (E : List (ℕ × ℕ)) (y : ℕ) : ℕ := enc16 ((xyE E).map fun e => dgt n 4 y (yEnd e))

lemma enc16_inj : ∀ (l1 l2 : List ℕ), l1.length = l2.length → (∀ d ∈ l1, d < 16) → (∀ d ∈ l2, d < 16) →
    enc16 l1 = enc16 l2 → l1 = l2
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | a :: l1, b :: l2, hl, h1, h2, he => by
    simp only [enc16, List.foldr_cons] at he
    have ha := h1 a List.mem_cons_self
    have hb := h2 b List.mem_cons_self
    have hab : a = b := by omega
    have hr : enc16 l1 = enc16 l2 := by unfold enc16; omega
    rw [hab, enc16_inj l1 l2 (by simpa using hl) (fun d hd => h1 d (List.mem_cons_of_mem _ hd))
      (fun d hd => h2 d (List.mem_cons_of_mem _ hd)) hr]

lemma dgt_lt16 {n : ℕ} (hn : 0 < n ∧ n ≤ 16) (x s : ℕ) : dgt n 4 x s < 16 :=
  lt_of_lt_of_le (Nat.mod_lt _ hn.1) hn.2

lemma key_iff {n : ℕ} (hn : 0 < n ∧ n ≤ 16) (E : List (ℕ × ℕ)) (x y : ℕ) :
    keyX n E x = keyY n E y ↔ ∀ e ∈ xyE E, dgt n 4 x (xEnd e) = dgt n 4 y (yEnd e) := by
  constructor
  · intro h
    have := enc16_inj _ _ (by simp) (by simp only [List.mem_map]; rintro _ ⟨e, -, rfl⟩; exact dgt_lt16 hn _ _)
      (by simp only [List.mem_map]; rintro _ ⟨e, -, rfl⟩; exact dgt_lt16 hn _ _) h
    exact List.map_inj_left.1 this
  · intro h
    unfold keyX keyY
    rw [List.map_inj_left.2 h]

lemma condE_iff (n : ℕ) (E : List (ℕ × ℕ)) (x y : ℕ) :
    (∀ e ∈ E, appDig n x y e.1 = appDig n x y e.2) ↔
      (∀ e ∈ xxE E, dgt n 4 x e.1 = dgt n 4 x e.2) ∧ (∀ e ∈ yyE E, dgt n 4 y (e.1 - 4) = dgt n 4 y (e.2 - 4)) ∧
        (∀ e ∈ xyE E, dgt n 4 x (xEnd e) = dgt n 4 y (yEnd e)) := by
  simp only [xxE, yyE, xyE, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, bne_iff_ne, ne_eq]
  constructor
  · intro h
    refine ⟨fun e ⟨he, h1, h2⟩ => ?_, fun e ⟨he, h1, h2⟩ => ?_, fun e ⟨he, h12⟩ => ?_⟩
    · have := h e he; simpa [appDig, h1, h2] using this
    · have := h e he; simpa [appDig, h1, h2] using this
    · have := h e he
      by_cases h1 : e.1 < 4
      · have h2 : ¬ e.2 < 4 := fun h2 => h12 (by simp [h1, h2])
        simpa [appDig, xEnd, yEnd, h1, h2] using this
      · have h2 : e.2 < 4 := by by_contra h2; exact h12 (by simp [h1, h2])
        simpa [appDig, xEnd, yEnd, h1, h2] using this.symm
  · rintro ⟨hx, hy, hm⟩ e he
    by_cases h1 : e.1 < 4 <;> by_cases h2 : e.2 < 4
    · simpa [appDig, h1, h2] using hx e ⟨he, h1, h2⟩
    · simpa [appDig, xEnd, yEnd, h1, h2] using hm e ⟨he, by simp [h1, h2]⟩
    · simpa [appDig, xEnd, yEnd, h1, h2] using (hm e ⟨he, by simp [h1, h2]⟩).symm
    · simpa [appDig, h1, h2] using hy e ⟨he, h1, h2⟩

/-- **The entry-rule condition, split**: x-only edges, y-only edges, keyed mixed edges. -/
theorem condE_split {n : ℕ} (hn : 0 < n ∧ n ≤ 16) (E : List (ℕ × ℕ)) (x y : ℕ) :
    (E.all fun e => appDig n x y e.1 == appDig n x y e.2) =
      (okX n E x && okY n E y && keyX n E x == keyY n E y) := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, beq_iff_eq, Bool.and_eq_true, okX, okY]
  rw [key_iff hn, condE_iff]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

lemma condF_edges (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) (x y : ℕ) :
    condF n kpos lpos p x y = (edgesR kpos lpos p).all fun e => appDig n x y e.1 == appDig n x y e.2 := by
  unfold condF edgesR
  rw [List.all_map]
  rfl

/-- The pairs of nonzero rows `(a.2, b.2)` joined by the edges `E`: x-only and y-only edges filter, mixed edges join
by key. -/
def pairsE (n : ℕ) (E : List (ℕ × ℕ)) (S : List (ℕ × List Int)) : List (List Int × List Int) :=
  let SX := (S.filter fun a => okX n E a.1).map fun a => (keyX n E a.1, a.2)
  let SY := (S.filter fun b => okY n E b.1).map fun b => (keyY n E b.1, b.2)
  SX.flatMap fun a => (SY.filter fun b => a.1 == b.1).map fun b => (a.2, b.2)

lemma pairsE_sum {n : ℕ} (hn : 0 < n ∧ n ≤ 16) (E : List (ℕ × ℕ)) (S : List (ℕ × List Int))
    (f : List Int → List Int → ℤ) :
    ((pairsE n E S).map fun rs => f rs.1 rs.2).sum = (S.map fun a => (S.map fun b =>
      if (E.all fun e => appDig n a.1 b.1 e.1 == appDig n a.1 b.1 e.2) then f a.2 b.2 else 0).sum).sum := by
  simp only [condE_split hn]
  unfold pairsE
  simp only []
  rw [list_sum_flatMap_map, List.map_map, list_sum_filter_map]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  simp only [Function.comp_apply, List.map_map, list_sum_filter_map]
  by_cases ha : okX n E a.1 = true
  · rw [ite_eq_left ha]
    refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
    simp only [ha, Bool.true_and]
    by_cases hb : okY n E b.1 = true
    · simp [hb]
    · simp [hb]
  · rw [ite_eq_right ha]
    simp [ha]

/-- Local rows from the nonzero rows `S` of `J` (`S = spRows (n^4) J`, `localRowsF_sp`). -/
def localRowsSp (n dim : ℕ) (S : List (ℕ × List Int)) (kpos lpos : List ℕ) : List (List SInt) :=
  (List.finRange 24).map fun p =>
    let pr := pairsE n (edgesR kpos lpos p) S
    (List.range (dim * dim)).map fun k =>
      SInt.ofInt ((pr.map fun rs => rs.1.getD (k / dim) 0 * rs.2.getD (k % dim) 0).sum)

/-- **Local rows from the nonzero rows of `J`.** -/
theorem localRowsF_sp (md : ModD) (kpos lpos : List ℕ) (hn : 0 < md.n ∧ md.n ≤ 16) :
    localRowsF md kpos lpos = localRowsSp md.n md.dim (spRows (md.n ^ 4) md.J) kpos lpos := by
  unfold localRowsF localRowsSp
  refine List.map_congr_left fun p _ => List.map_congr_left fun k _ => ?_
  congr 1
  rw [kmatF_sp, pairsE_sum hn _ _ (fun r s => r.getD (k / md.dim) 0 * s.getD (k % md.dim) 0)]
  simp only [condF_edges]

/-- **`mkTab` from the nonzero rows of every module.** -/
theorem mkTab_sp (C : CertD) (kpos lpos : List ℕ)
    (hn : C.mods.all (fun md => decide (0 < md.n) && decide (md.n ≤ 16)) = true) :
    mkTab C kpos lpos (supps 2 kpos lpos) (supps 3 kpos lpos) =
      C.mods.map fun md => localRowsSp md.n md.dim (spRows (md.n ^ 4) md.J) kpos lpos := by
  rw [mkTab_eq]
  refine List.map_congr_left fun md hmd => localRowsF_sp md kpos lpos ?_
  have := List.all_eq_true.1 hn md hmd
  simpa using this

/-- Lists from their entries (assembly of per-entry kernel checks). -/
lemma map_eq_of_getD {α β : Type*} [Inhabited α] (f : α → β) (L : List α) (T : List β) (d : β)
    (hl : L.length = T.length) (h : ∀ i < L.length, f (L.getD i default) = T.getD i d) : L.map f = T := by
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  have h1' : i < L.length := by simpa using h1
  have := h i h1'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1', Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this
  simpa using this

/-! ### `del` entries -/

/-- Digit `t` of the 4-digit string with survivor digits `u` (flat, 3 digits) and traced digit `z`. -/
def digE (n slot : ℕ) (order : List ℕ) (u z t : ℕ) : ℕ := if t = slot then z else dgt n 3 u (order.idxOf t % 3)

/-- `pf p j` on naturals. -/
def pfN (p j : ℕ) : ℕ := (permL.getD p []).getD j 0 % 4

/-- Flat index of `a ∘ pf p ∘ oF order` for that string. -/
def f2E (n slot : ℕ) (order : List ℕ) (p u z : ℕ) : ℕ :=
  ((List.range 3).map fun v => digE n slot order u z (pfN p (order.getD v 0 % 4)) * n ^ (2 - v)).sum

/-- Row `x` among the nonzero rows (`[]` if absent). -/
def lookRow (S : List (ℕ × List Int)) (x : ℕ) : List Int :=
  match S.find? (fun a => a.1 == x) with
  | some a => a.2
  | none => []

/-- `delFast` from the nonzero rows `S` of `J` (`delFast_sp`): survivors `u` over the nonzero rows, traced digit `z`. -/
def delSp (S : List (ℕ × List Int)) (slot : ℕ) (order : List ℕ) (n p μ ν : ℕ) : ℤ :=
  (S.map fun a => ((List.range n).map fun z =>
    if digE n slot order a.1 z slot = digE n slot order a.1 z (pfN p slot) then
      a.2.getD μ 0 * (lookRow S (f2E n slot order p a.1 z)).getD ν 0 else 0).sum).sum

lemma lookRow_aux (N ν : ℕ) : ∀ (rs : List (List Int)) (i : ℕ), i + rs.length ≤ N → ∀ x,
    (lookRow (spRowsAux N i rs) x).getD ν 0 = if i ≤ x then (rs.getD (x - i) []).getD ν 0 else 0
  | [], i, _, x => by simp [spRowsAux, lookRow]
  | r :: rs, i, hl, x => by
    simp only [List.length_cons] at hl
    have ih := lookRow_aux N ν rs (i + 1) (by omega) x
    have hiN : i < N := by omega
    simp only [spRowsAux]
    by_cases hr : r.any (· != 0) = true
    · rw [ite_eq_left ⟨hiN, hr⟩]
      by_cases hx : i = x
      · subst hx
        simp [lookRow, List.find?_cons_of_pos]
      · have hne : ¬ (((i, r) : ℕ × List Int).1 == x) = true := by simpa using hx
        have e : lookRow ((i, r) :: spRowsAux N (i + 1) rs) x = lookRow (spRowsAux N (i + 1) rs) x := by
          unfold lookRow
          rw [List.find?_cons_of_neg]
          exact hne
        rw [e, ih]
        by_cases hix : i + 1 ≤ x
        · rw [ite_eq_left hix, ite_eq_left (by omega : i ≤ x), show x - i = (x - (i + 1)) + 1 by omega,
            List.getD_cons_succ]
        · rw [ite_eq_right hix, ite_eq_right (by omega : ¬ i ≤ x)]
    · rw [ite_eq_right (fun h => hr h.2), ih]
      by_cases hix : i + 1 ≤ x
      · rw [ite_eq_left hix, ite_eq_left (by omega : i ≤ x), show x - i = (x - (i + 1)) + 1 by omega,
          List.getD_cons_succ]
      · rw [ite_eq_right hix]
        by_cases hx : i = x
        · subst hx
          rw [ite_eq_left le_rfl, Nat.sub_self, List.getD_cons_zero, getD_zero_of_any hr]
        · rw [ite_eq_right (by omega : ¬ i ≤ x)]

/-- Rows looked up among the nonzero rows (all rows of `J` have index `< N`). -/
lemma lookRow_spRows (N ν : ℕ) (J : List (List Int)) (hJ : J.length ≤ N) (x : ℕ) :
    (lookRow (spRows N J) x).getD ν 0 = (J.getD x []).getD ν 0 := by
  rw [spRows, lookRow_aux N ν J 0 (by simpa using hJ) x]
  simp

section Del

variable {slot : ℕ} {order : List ℕ}

lemma splitE_symm_val (h : SOk slot order) {n : ℕ} [NeZero n] (u : ℕ) (z : Fin n) (t : Fin 4) :
    ((splitE h).symm (z, unflat n 3 u) t).val = digE n slot order u z.val t.val := by
  show ((if t = sF slot then z else unflat n 3 u (iF order t)) : Fin n).val = _
  unfold digE
  have ht : t = sF slot ↔ t.val = slot := by
    constructor
    · intro e; rw [e]; exact Nat.mod_eq_of_lt h.1
    · intro e; apply Fin.ext; rw [e]; exact (Nat.mod_eq_of_lt h.1).symm
  by_cases h' : t = sF slot
  · rw [ite_eq_left h', ite_eq_left (ht.1 h')]
  · rw [ite_eq_right h', ite_eq_right (fun e => h' (ht.2 e))]
    rfl

lemma splitE_symm_oF (h : SOk slot order) {n : ℕ} [NeZero n] (u : ℕ) (hu : u < n ^ 3) (z : Fin n) :
    flat ((splitE h).symm (z, unflat n 3 u) ∘ oF order) = u := by
  have e : (splitE h).symm (z, unflat n 3 u) ∘ oF order = unflat n 3 u :=
    congrArg Prod.snd ((splitE h).apply_symm_apply (z, unflat n 3 u))
  rw [e, flat_unflat u hu]

lemma flat_f2 (h : SOk slot order) {n : ℕ} [NeZero n] (p : Fin 24) (u : ℕ) (z : Fin n) :
    flat ((splitE h).symm (z, unflat n 3 u) ∘ pf p ∘ oF order) = f2E n slot order p.val u z.val := by
  unfold flat f2E
  rw [Fin.sum_univ_three]
  simp only [Function.comp_apply, splitE_symm_val h]
  have e3 : List.range 3 = [0, 1, 2] := rfl
  rw [e3]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [add_assoc]
  rfl

lemma cond_split (h : SOk slot order) {n : ℕ} [NeZero n] (p : Fin 24) (u : ℕ) (z : Fin n) :
    (splitE h).symm (z, unflat n 3 u) (sF slot) = (splitE h).symm (z, unflat n 3 u) (pf p (sF slot)) ↔
      digE n slot order u z.val slot = digE n slot order u z.val (pfN p.val slot) := by
  have h1 : (sF slot).val = slot := Nat.mod_eq_of_lt h.1
  rw [Fin.ext_iff, splitE_symm_val h, splitE_symm_val h, h1]
  show _ = digE n slot order u z.val (pfN p.val (sF slot).val) ↔ _
  rw [h1]

/-- **`delFast` from the nonzero rows of `J`** (`J` with at most `n^3` rows). -/
theorem delFast_sp (h : SOk slot order) (J : List (List Int)) (n : ℕ) [NeZero n] (hJ : J.length ≤ n ^ 3)
    (p : Fin 24) (μ ν : ℕ) :
    delFast J slot order n p μ ν = delSp (spRows (n ^ 3) J) slot order n p.val μ ν := by
  set S := spRows (n ^ 3) J
  let G : (Fin 4 → Fin n) → ℤ := fun a => if a (sF slot) = a (pf p (sF slot)) then
      (J.getD (flat (a ∘ oF order)) []).getD μ 0 * (J.getD (flat (a ∘ pf p ∘ oF order)) []).getD ν 0 else 0
  let F : ℕ → List Int → ℤ := fun u r => ((List.range n).map fun z =>
    if digE n slot order u z slot = digE n slot order u z (pfN p.val slot) then
      r.getD μ 0 * (lookRow S (f2E n slot order p.val u z)).getD ν 0 else 0).sum
  have hF : ∀ u r, (∀ μ, r.getD μ 0 = 0) → F u r = 0 := by
    intro u r hr
    simp only [F, hr, zero_mul, ite_self, List.map_const', List.sum_replicate, smul_zero]
  have e1 : delFast J slot order n p μ ν = ∑ a, G a := by
    unfold delFast
    rw [sum_fun_range G]
  have e2 : ∑ a, G a = ∑ u ∈ range (n ^ 3), F u (J.getD u []) := by
    rw [← (splitE h).symm.sum_comp G, Fintype.sum_prod_type, Finset.sum_comm, sum_fun_range]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u < n ^ 3 := Finset.mem_range.1 hu
    simp only [F]
    rw [← finset_sum_range_listZ, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [G]
    rw [splitE_symm_oF h u hu' z, flat_f2 h p u z]
    by_cases hc : digE n slot order u z.val slot = digE n slot order u z.val (pfN p.val slot)
    · rw [ite_eq_left ((cond_split h p u z).2 hc), ite_eq_left hc, lookRow_spRows _ _ J hJ]
    · rw [ite_eq_right (fun e => hc ((cond_split h p u z).1 e)), ite_eq_right hc]
  rw [e1, e2, ← sum_spRows (n ^ 3) J F hF]
  rfl

end Del

/-- `eqLocF` with `delFast` evaluated over the nonzero rows (`eqLocS_eq`). -/
def eqLocS (C : CertD) (sp : EqSpecD) (n : ℕ) (p : Fin 24) (o : ℕ) : ℤ :=
  let dec := C.eqDecode sp.mkeys o
  let md := C.mods.getD (sp.mkeys.getD dec.1 0) default
  if dec.2.1 < md.dim then if dec.2.2 < md.dim then
    if sp.kind = 0 then
      if hn : n = 0 then 0 else
        haveI : NeZero n := ⟨hn⟩
        if SOk sp.slot sp.order then
          (if md.J.length ≤ n ^ 3 then delSp (spRows (n ^ 3) md.J) sp.slot sp.order n p.val dec.2.1 dec.2.2
            else delFast md.J sp.slot sp.order n p dec.2.1 dec.2.2)
        else delB md.J sp.slot sp.order n p dec.2.1 dec.2.2
    else stiefF md.J sp.slot p dec.2.1 dec.2.2
  else 0 else 0

lemma eqLocS_eq (C : CertD) (sp : EqSpecD) (n : ℕ) (p : Fin 24) (o : ℕ) : eqLocS C sp n p o = eqLocF C sp n p o := by
  unfold eqLocS eqLocF
  dsimp only
  generalize C.eqDecode sp.mkeys o = dec
  generalize C.mods.getD (sp.mkeys.getD dec.1 0) default = md
  split_ifs with hμ hν hk hn hso hJ
  all_goals first
    | rfl
    | (have : NeZero n := ⟨hn⟩; exact (delFast_sp hso md.J n hJ p _ _).symm)

/-- Equality tables over the nonzero rows (`eqTabOf_sp`). -/
def eqTabSp (C : CertD) (sp : EqSpecD) (n N : ℕ) : List (List ℤ) :=
  (List.finRange 24).map fun p => (List.range N).map fun o => eqLocS C sp n p o

/-- **Equality tables from the nonzero rows.** -/
theorem eqTabOf_sp (C : CertD) (sp : EqSpecD) (n N : ℕ) : eqTabOf C sp n N = eqTabSp C sp n N := by
  unfold eqTabOf eqTabSp
  simp only [eqLocS_eq]

end NPT.Cert.Ident
