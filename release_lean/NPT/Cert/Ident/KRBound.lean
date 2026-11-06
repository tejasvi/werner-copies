/-
NPT.Cert.Ident.KRBound — a crude a-priori bound on the word values of a family, cheap to evaluate in the kernel
(for the mod-p kernel identity check): it computes no local rows and no leaf tensors, only maxima of
the certificate data.

`partsF_le_crudeB : |partsF (famParts C zmul f gs zs za eqT) w0 w1 w2 w3| ≤ crudeB C zmul f gs zs za` for all words
`w_l < 24`, provided every equality-map value is at most `eqB C n` (true for `eqT = eqLocF C`: `eqLocF_le`), where

  `crudeB = crudeN · crudeK · crudeV`  (term count × max coefficient × max value):
* `crudeN` (number of terms): per rule-group item `nb² · (dim² · n^8)^4` (block size `nb`, module dimension `dim` and
  local dimension `n` at their maxima: the item's `W Zq Wᵀ` sum and the four local-row sums over all digit pairs),
  plus `1` for the objective (family 0) and `1` per equality-multiplier entry;
* `crudeK` (largest coefficient): `max(den3 · max|Zq|, 2 Lden, max |sign · den3 · λ|)`;
* `crudeV` (largest value): `max(max|W|² · max|J|^8, max|zs|³ · max|za|, eqB(d)³ · eqB(2))`.

The maxima are recursor-encoded (`List.rec`, `Bool.rec`, `Nat.ble`) for the kernel, so the definitions are
`noncomputable` (no `#eval`; `decide +kernel` is unaffected). Kernel cost on EP3D3: `crudeB … < 2 ^ 5900` for all
three families in one `decide +kernel`: 54 s, 4 GB. Almost all of it is the block scan `zqBmax`; `crudeBZ` and
`partsF_le_crudeBZ_eqLocF` let that scan be checked once (`zqBmax C zmul ≤ Z`) and each family's bound separately.
-/
import NPT.Cert.Ident.IdFactGen

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

noncomputable section

/-! ### Maxima -/

/-- Largest element (0 for the empty list); recursor-encoded (`List.rec`, `Bool.rec`, `Nat.ble`) so that the kernel
evaluates it in linear time. -/
noncomputable def maxNat (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0 (fun x _ ih => @Bool.rec (fun _ => ℕ) x ih (Nat.ble x ih)) l

lemma maxNat_nil : maxNat [] = 0 := rfl

lemma bmax_eq (x y : ℕ) : @Bool.rec (fun _ => ℕ) x y (Nat.ble x y) = max x y := by
  cases h : Nat.ble x y
  · have : ¬ x ≤ y := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; cases h
    show x = max x y
    rw [max_def, ite_eq_right this]
  · have : x ≤ y := Nat.le_of_ble_eq_true h
    show y = max x y
    rw [max_def, ite_eq_left this]

lemma maxNat_cons (x : ℕ) (xs : List ℕ) : maxNat (x :: xs) = max x (maxNat xs) := bmax_eq x (maxNat xs)

lemma le_maxNat {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ maxNat l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [maxNat_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma maxNat_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : maxNat l ≤ B := by
  induction l with
  | nil => simp [maxNat_nil]
  | cons a l ih =>
    rw [maxNat_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

lemma getD_ge {α : Type*} (l : List α) (d : α) (n : ℕ) (h : l.length ≤ n) : l.getD n d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

/-- Largest `|entry|` of a row (recursor-encoded). -/
noncomputable def rowMaxI (r : List ℤ) : ℕ :=
  @List.rec ℤ (fun _ => ℕ) 0 (fun x _ ih => @Bool.rec (fun _ => ℕ) (Int.natAbs x) ih (Nat.ble (Int.natAbs x) ih)) r

/-- Largest `|entry|` of a matrix given by rows (recursor-encoded). -/
noncomputable def maxAbsI (rows : List (List ℤ)) : ℕ :=
  @List.rec (List ℤ) (fun _ => ℕ) 0 (fun r _ ih => @Bool.rec (fun _ => ℕ) (rowMaxI r) ih (Nat.ble (rowMaxI r) ih)) rows

lemma rowMaxI_eq : ∀ (r : List ℤ), rowMaxI r = maxNat (r.map Int.natAbs)
  | [] => rfl
  | x :: r => by
    show @Bool.rec (fun _ => ℕ) (Int.natAbs x) (rowMaxI r) (Nat.ble (Int.natAbs x) (rowMaxI r)) = _
    rw [bmax_eq, List.map_cons, maxNat_cons, rowMaxI_eq r]

lemma maxAbsI_eq : ∀ (rows : List (List ℤ)), maxAbsI rows = maxNat (rows.map fun r => maxNat (r.map Int.natAbs))
  | [] => rfl
  | r :: rows => by
    show @Bool.rec (fun _ => ℕ) (rowMaxI r) (maxAbsI rows) (Nat.ble (rowMaxI r) (maxAbsI rows)) = _
    rw [bmax_eq, List.map_cons, maxNat_cons, maxAbsI_eq rows, rowMaxI_eq r]

lemma natAbs_getD_le (rows : List (List ℤ)) (i j : ℕ) : ((rows.getD i []).getD j 0).natAbs ≤ maxAbsI rows := by
  rw [maxAbsI_eq]
  rcases Nat.lt_or_ge i rows.length with hi | hi
  · rcases Nat.lt_or_ge j (rows.getD i []).length with hj | hj
    · have h1 : ((rows.getD i []).getD j 0).natAbs ≤ maxNat ((rows.getD i []).map Int.natAbs) :=
        le_maxNat (List.mem_map.2 ⟨_, getD_mem_of_lt _ _ _ hj, rfl⟩)
      exact le_trans h1 (le_maxNat (List.mem_map.2 ⟨_, getD_mem_of_lt _ _ _ hi, rfl⟩))
    · rw [getD_ge _ _ _ hj]; simp
  · rw [getD_ge _ _ _ hi]; simp

lemma abs_getD_le (rows : List (List ℤ)) (i j : ℕ) : |(rows.getD i []).getD j 0| ≤ (maxAbsI rows : ℤ) := by
  rw [Int.abs_eq_natAbs]; exact_mod_cast natAbs_getD_le rows i j

/-! ### Local rows -/

lemma abs_kmatF_le (n : ℕ) (J : List (List ℤ)) (kpos lpos : List ℕ) (p : Fin 24) (μ ν : ℕ) :
    |kmatF n J kpos lpos p μ ν| ≤ ((n ^ 4 * n ^ 4 * maxAbsI J ^ 2 : ℕ) : ℤ) := by
  unfold kmatF
  have hterm : ∀ xi yi, |(J.getD xi []).getD μ 0 * (J.getD yi []).getD ν 0 *
      (if condF n kpos lpos p xi yi then 1 else 0)| ≤ ((maxAbsI J ^ 2 : ℕ) : ℤ) := by
    intro xi yi
    rw [abs_mul, abs_mul]
    have h1 := abs_getD_le J xi μ
    have h2 := abs_getD_le J yi ν
    have h3 : |(if condF n kpos lpos p xi yi then (1 : ℤ) else 0)| ≤ 1 := by split_ifs <;> simp
    push_cast
    calc |(J.getD xi []).getD μ 0| * |(J.getD yi []).getD ν 0| * |(if condF n kpos lpos p xi yi then (1 : ℤ) else 0)|
        ≤ (maxAbsI J : ℤ) * maxAbsI J * 1 := by
          apply mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3 (abs_nonneg _) (by positivity)
      _ = (maxAbsI J : ℤ) ^ 2 := by ring
  calc |∑ xi ∈ range (n ^ 4), ∑ yi ∈ range (n ^ 4), (J.getD xi []).getD μ 0 * (J.getD yi []).getD ν 0 *
        (if condF n kpos lpos p xi yi then 1 else 0)|
      ≤ ∑ xi ∈ range (n ^ 4), ∑ yi ∈ range (n ^ 4), |(J.getD xi []).getD μ 0 * (J.getD yi []).getD ν 0 *
        (if condF n kpos lpos p xi yi then 1 else 0)| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun xi _ => ?_)
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ xi ∈ range (n ^ 4), ∑ yi ∈ range (n ^ 4), ((maxAbsI J ^ 2 : ℕ) : ℤ) :=
        Finset.sum_le_sum fun xi _ => Finset.sum_le_sum fun yi _ => hterm xi yi
    _ = ((n ^ 4 * n ^ 4 * maxAbsI J ^ 2 : ℕ) : ℤ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

lemma SInt.mag_ofInt (z : ℤ) : (SInt.ofInt z).mag = z.natAbs := by cases z <;> rfl

/-- Crude bound on the row sums of a module's local rows: `dim² · n^8 · max|J|²`. -/
def rowB (md : ModD) : ℕ := md.dim * md.dim * (md.n ^ 4 * md.n ^ 4 * maxAbsI md.J ^ 2)

lemma foldrMax_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

lemma rowAbs_le {A : List (List SInt)} {B : ℕ} (h : ∀ row ∈ A, (row.map SInt.mag).sum ≤ B) : rowAbs A ≤ B := by
  unfold rowAbs
  exact foldrMax_le (l := A.map fun row => (row.map SInt.mag).sum) fun x hx => by
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.1 hx; exact h row hrow

lemma rowAbs_localRowsF_le (md : ModD) (kpos lpos : List ℕ) : rowAbs (localRowsF md kpos lpos) ≤ rowB md := by
  apply rowAbs_le
  intro row hrow
  unfold localRowsF at hrow
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hrow
  rw [List.map_map]
  have hk : ∀ k ∈ List.range (md.dim * md.dim), (SInt.mag ∘ fun k => SInt.ofInt (kmatF md.n md.J kpos lpos p
      (k / md.dim) (k % md.dim))) k ≤ md.n ^ 4 * md.n ^ 4 * maxAbsI md.J ^ 2 := by
    intro k _
    have h := abs_kmatF_le md.n md.J kpos lpos p (k / md.dim) (k % md.dim)
    rw [Int.abs_eq_natAbs] at h
    show (SInt.ofInt _).mag ≤ _
    rw [SInt.mag_ofInt]
    exact_mod_cast h
  calc ((List.range (md.dim * md.dim)).map (SInt.mag ∘ fun k => SInt.ofInt (kmatF md.n md.J kpos lpos p
        (k / md.dim) (k % md.dim)))).sum
      ≤ ((List.range (md.dim * md.dim)).map fun _ => md.n ^ 4 * md.n ^ 4 * maxAbsI md.J ^ 2).sum :=
        List.sum_le_sum fun k hk' => hk k hk'
    _ = rowB md := by simp [rowB, List.sum_replicate, List.map_const']

/-! ### Items -/

/-- Bound on `|zqI b zmul a c|`: `max|zrows| · zmul + 2 · max|uent value|`. -/
def zqB (b : NPT.Cert.PBlock) (zmul : ℕ) : ℕ :=
  maxAbsI b.zrows * zmul + 2 * maxNat (b.uent.map fun e => e.2.2.natAbs)

lemma abs_zqI_le (b : NPT.Cert.PBlock) (zmul a c : ℕ) : |zqI b zmul a c| ≤ (zqB b zmul : ℤ) := by
  unfold zqI zqB
  have h1 : |b.zget a c * (zmul : ℤ)| ≤ (maxAbsI b.zrows : ℤ) * zmul := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ zmul)]
    exact mul_le_mul_of_nonneg_right (abs_getD_le b.zrows a c) (by positivity)
  have h2 : |(match b.ufind a c with | some e => 2 * e.2.2 | none => (0 : ℤ))| ≤
      2 * (maxNat (b.uent.map fun e => e.2.2.natAbs) : ℤ) := by
    cases hf : b.ufind a c with
    | none => simp
    | some e =>
      have hmem : e ∈ b.uent := List.mem_of_find?_eq_some hf
      have hle : e.2.2.natAbs ≤ maxNat (b.uent.map fun e => e.2.2.natAbs) := le_maxNat (List.mem_map.2 ⟨e, hmem, rfl⟩)
      simp only
      rw [abs_mul, Int.abs_eq_natAbs e.2.2]
      have : (e.2.2.natAbs : ℤ) ≤ maxNat (b.uent.map fun e => e.2.2.natAbs) := by exact_mod_cast hle
      norm_num
      linarith
  push_cast
  calc |b.zget a c * (zmul : ℤ) + (match b.ufind a c with | some e => 2 * e.2.2 | none => 0)|
      ≤ |b.zget a c * (zmul : ℤ)| + |(match b.ufind a c with | some e => 2 * e.2.2 | none => (0 : ℤ))| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- A bound on every entry of a matrix bounds each `getD` entry. -/
lemma abs_getD_le_of (rows : List (List ℤ)) (B : ℤ) (hB : 0 ≤ B) (h : ∀ r ∈ rows, ∀ x ∈ r, |x| ≤ B) (i j : ℕ) :
    |(rows.getD i []).getD j 0| ≤ B := by
  rcases Nat.lt_or_ge i rows.length with hi | hi
  · rcases Nat.lt_or_ge j (rows.getD i []).length with hj | hj
    · exact h _ (getD_mem_of_lt _ _ _ hi) _ (getD_mem_of_lt _ _ _ hj)
    · rw [getD_ge _ _ _ hj]; simpa using hB
  · rw [getD_ge _ _ _ hi]; simpa using hB

/-- Bound on every entry of `itemTF C zmul coef … it`: `nb² · (|coef| · max|Zq|) · max|W|²` (block size `nb`). -/
def itemB (C : CertD) (zmul : ℕ) (coef : ℤ) (it : ℕ × ℕ × ℕ) : ℕ :=
  (C.Z.getD (C.types.getD it.1 default).zi default).n * (C.Z.getD (C.types.getD it.1 default).zi default).n *
    (coef.natAbs * zqB (C.Z.getD (C.types.getD it.1 default).zi default) zmul) *
    maxAbsI (C.types.getD it.1 default).W ^ 2

lemma abs_itemY_le (C : CertD) (zmul d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (v a : ℕ) :
    |((itemY C zmul d0 d1 d2 d3 it).getD v []).getD a 0| ≤
      ((C.Z.getD (C.types.getD it.1 default).zi default).n *
        zqB (C.Z.getD (C.types.getD it.1 default).zi default) zmul * maxAbsI (C.types.getD it.1 default).W : ℕ) := by
  set t := C.types.getD it.1 default
  set b := C.Z.getD t.zi default
  refine abs_getD_le_of _ _ (by positivity) ?_ v a
  intro r hr x hx
  unfold itemY at hr
  obtain ⟨v', -, rfl⟩ := List.mem_map.1 hr
  obtain ⟨a', -, rfl⟩ := List.mem_map.1 hx
  calc |∑ c ∈ range b.n, zqI b zmul a' c * (t.W.getD (it.2.2 * (d0 * d1 * d2 * d3) + v') []).getD c 0|
      ≤ ∑ c ∈ range b.n, |zqI b zmul a' c * (t.W.getD (it.2.2 * (d0 * d1 * d2 * d3) + v') []).getD c 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ range b.n, (zqB b zmul : ℤ) * maxAbsI t.W := Finset.sum_le_sum fun c _ => by
        rw [abs_mul]
        exact mul_le_mul (abs_zqI_le b zmul a' c) (abs_getD_le _ _ _) (abs_nonneg _) (by positivity)
    _ = ((b.n * zqB b zmul * maxAbsI t.W : ℕ) : ℤ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

lemma abs_itemE_le (C : CertD) (zmul : ℕ) (coef : ℤ) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (i0 i1 i2 i3 : ℕ) :
    |itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it) i0 i1 i2 i3| ≤ (itemB C zmul coef it : ℤ) := by
  set t := C.types.getD it.1 default
  set b := C.Z.getD t.zi default
  unfold itemE
  simp only
  rw [abs_mul]
  have hsum : |∑ a ∈ range b.n, (t.W.getD (it.2.1 * (d0 * d1 * d2 * d3) +
      mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)) []).getD a 0 *
      ((itemY C zmul d0 d1 d2 d3 it).getD (mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)) []).getD a 0| ≤
      ((b.n * (b.n * zqB b zmul * maxAbsI t.W) * maxAbsI t.W : ℕ) : ℤ) := by
    calc _ ≤ ∑ a ∈ range b.n, |(t.W.getD (it.2.1 * (d0 * d1 * d2 * d3) +
          mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)) []).getD a 0 *
          ((itemY C zmul d0 d1 d2 d3 it).getD (mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)) []).getD a 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ range b.n, (maxAbsI t.W : ℤ) * ((b.n * zqB b zmul * maxAbsI t.W : ℕ) : ℤ) :=
          Finset.sum_le_sum fun a _ => by
            rw [abs_mul]
            exact mul_le_mul (abs_getD_le _ _ _) (abs_itemY_le C zmul d0 d1 d2 d3 it _ a) (abs_nonneg _)
              (by positivity)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  calc |coef| * |∑ a ∈ range b.n, (t.W.getD (it.2.1 * (d0 * d1 * d2 * d3) +
        mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)) []).getD a 0 *
        ((itemY C zmul d0 d1 d2 d3 it).getD (mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)) []).getD a 0|
      ≤ (coef.natAbs : ℤ) * ((b.n * (b.n * zqB b zmul * maxAbsI t.W) * maxAbsI t.W : ℕ) : ℤ) := by
        rw [Int.abs_eq_natAbs coef]; exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (itemB C zmul coef it : ℤ) := by unfold itemB; push_cast; ring

lemma maxAbs_itemTF_le (C : CertD) (zmul : ℕ) (coef : ℤ) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    maxAbs (itemTF C zmul coef d0 d1 d2 d3 it) ≤ itemB C zmul coef it := by
  unfold maxAbs
  refine foldrMax_le (l := (itemTF C zmul coef d0 d1 d2 d3 it).map SInt.mag) fun x hx => ?_
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
  unfold itemTF at hs
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hs
  obtain ⟨i0, -, i1, -, i2, -, i3, -, rfl⟩ := hs
  rw [SInt.mag_ofInt]
  have := abs_itemE_le C zmul coef d0 d1 d2 d3 it i0 i1 i2 i3
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this

lemma SInt.mag_add_le (x y : SInt) : (x.add y).mag ≤ x.mag + y.mag := by
  have h : |(x.add y).val| ≤ |x.val| + |y.val| := by rw [SInt.val_add]; exact abs_add_le _ _
  rw [SInt.abs_val, SInt.abs_val, SInt.abs_val] at h
  exact_mod_cast h

lemma maxAbs_cons (x : SInt) (xs : List SInt) : maxAbs (x :: xs) = max x.mag (maxAbs xs) := rfl

lemma maxAbs_addL_le : ∀ (xs ys : List SInt), maxAbs (addL xs ys) ≤ maxAbs xs + maxAbs ys
  | [], ys => by simp [addL, maxAbs]
  | x :: xs, [] => by simp [addL, maxAbs]
  | x :: xs, y :: ys => by
    simp only [addL, maxAbs_cons]
    have h1 := SInt.mag_add_le x y
    have h2 := maxAbs_addL_le xs ys
    refine max_le ?_ ?_
    · exact le_trans h1 (add_le_add (le_max_left _ _) (le_max_left _ _))
    · exact le_trans h2 (add_le_add (le_max_right _ _) (le_max_right _ _))

lemma maxAbs_foldr_addL_le {α : Type*} (g : α → List SInt) : ∀ (items : List α),
    maxAbs ((items.map g).foldr addL []) ≤ (items.map fun it => maxAbs (g it)).sum
  | [] => by simp [maxAbs]
  | a :: rest => by
    simp only [List.map_cons, List.foldr_cons, List.sum_cons]
    exact le_trans (maxAbs_addL_le _ _) (add_le_add le_rfl (maxAbs_foldr_addL_le g rest))

/-! ### Trees -/

section TreeBound

variable (S : Spec) (R : ℕ) (LB : Leaf → ℕ) (hR : ∀ m, rowAbs (S.rows m) ≤ R)
  (hL : ∀ m1 m2 m3 lf, maxAbs (S.leaf m1 m2 m3 lf) ≤ LB lf)
include hR hL

lemma boundLeaf_le' (m1 m2 m3 : ℕ) (lf : Leaf) : boundLeaf S m1 m2 m3 lf ≤ R * LB lf :=
  Nat.mul_le_mul (hR _) (hL _ _ _ _)

lemma boundNd1_le' (m2 m3 : ℕ) (nd : Nd1) : boundNd1 S m2 m3 nd ≤ R * (R * (nd.kids.map LB).sum) := by
  unfold boundNd1
  refine Nat.mul_le_mul (hR _) ?_
  rw [← List.sum_map_mul_left]
  exact List.sum_le_sum fun lf _ => boundLeaf_le' S R LB hR hL _ _ _ lf

lemma boundNd2_le' (m3 : ℕ) (nd : Nd2) :
    boundNd2 S m3 nd ≤ R * (R * (R * (nd.kids.map fun n1 => (n1.kids.map LB).sum).sum)) := by
  unfold boundNd2
  refine Nat.mul_le_mul (hR _) ?_
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left]
  refine List.sum_le_sum fun n1 _ => ?_
  have := boundNd1_le' S R LB hR hL nd.m2 m3 n1
  calc boundNd1 S nd.m2 m3 n1 ≤ R * (R * (n1.kids.map LB).sum) := this
    _ = R * (R * (n1.kids.map LB).sum) := rfl

lemma boundNd3_le' (nd : Nd3) :
    boundNd3 S nd ≤ R * (R * (R * (R * (nd.kids.map fun n2 => (n2.kids.map fun n1 => (n1.kids.map LB).sum).sum).sum))) := by
  unfold boundNd3
  refine Nat.mul_le_mul (hR _) ?_
  rw [← List.sum_map_mul_left, ← List.sum_map_mul_left, ← List.sum_map_mul_left]
  exact List.sum_le_sum fun n2 _ => boundNd2_le' S R LB hR hL nd.m3 n2

/-- **Tree bound**: `boundTree ≤ R⁴ · Σ_leaves LB`. -/
lemma boundTree_le' (tree : List Nd3) : boundTree S tree ≤ R ^ 4 *
    (tree.map fun n3 => (n3.kids.map fun n2 => (n2.kids.map fun n1 => (n1.kids.map LB).sum).sum).sum).sum := by
  unfold boundTree
  rw [← List.sum_map_mul_left]
  refine List.sum_le_sum fun n3 _ => ?_
  have := boundNd3_le' S R LB hR hL n3
  calc boundNd3 S n3 ≤ R * (R * (R * (R * _))) := this
    _ = R ^ 4 * _ := by ring

end TreeBound

lemma sum_flatMap' {α : Type*} (l : List α) (f : α → List ℕ) : (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma sum_itemsOf (g : ℕ × ℕ × ℕ → ℕ) (tree : List Nd3) : ((itemsOf tree).map g).sum =
    (tree.map fun n3 => (n3.kids.map fun n2 => (n2.kids.map fun n1 =>
      (n1.kids.map fun lf => (lf.items.map g).sum).sum).sum).sum).sum := by
  unfold itemsOf
  simp only [List.map_flatMap, sum_flatMap']

/-- **Rule-group bound**: `boundTree (ruleSpecF …) tree ≤ R⁴ · Σ_items itemB` for any `R` bounding all row sums. -/
lemma boundTree_ruleSpecF_le (C : CertD) (zmul : ℕ) (coef : ℤ) (kpos lpos : List ℕ) (R : ℕ)
    (hR : ∀ md ∈ C.mods, rowB md ≤ R) (tree : List Nd3) :
    boundTree (ruleSpecF C zmul coef kpos lpos) tree ≤ R ^ 4 * ((itemsOf tree).map (itemB C zmul coef)).sum := by
  rw [sum_itemsOf]
  refine boundTree_le' _ R (fun lf => (lf.items.map (itemB C zmul coef)).sum) (fun m => ?_) (fun m1 m2 m3 lf => ?_) tree
  · show rowAbs (localRowsF (C.mods.getD m default) kpos lpos) ≤ R
    refine le_trans (rowAbs_localRowsF_le _ _ _) ?_
    rcases Nat.lt_or_ge m C.mods.length with hm | hm
    · exact hR _ (getD_mem_of_lt _ _ _ hm)
    · rw [getD_ge _ _ _ hm, show rowB (default : ModD) = 0 from rfl]; exact Nat.zero_le R
  · show maxAbs ((lf.items.map (itemTF C zmul coef (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3))).foldr
      addL []) ≤ _
    refine le_trans (maxAbs_foldr_addL_le _ _) (List.sum_le_sum fun it _ => maxAbs_itemTF_le _ _ _ _ _ _ _ _)

/-! ### Rank-one parts -/

lemma rowAbs_rank1_le (E : ℕ → Fin 24 → ℤ) (c : ℤ) (l B : ℕ) (h : ∀ p, (E l p).natAbs ≤ B) :
    rowAbs ((rank1Spec E c).rows l) ≤ B := by
  apply rowAbs_le
  intro row hrow
  simp only [rank1Spec, List.mem_map] at hrow
  obtain ⟨p, -, rfl⟩ := hrow
  simp [SInt.mag_ofInt, h p]

lemma boundTree_rank1 (E : ℕ → Fin 24 → ℤ) (c : ℤ) :
    boundTree (rank1Spec E c) rank1Tree = rowAbs ((rank1Spec E c).rows 3) * (rowAbs ((rank1Spec E c).rows 2) *
      (rowAbs ((rank1Spec E c).rows 1) * (rowAbs ((rank1Spec E c).rows 0) * c.natAbs))) := by
  simp [boundTree, boundNd3, boundNd2, boundNd1, boundLeaf, rank1Tree, maxAbs, rank1Spec, SInt.mag_ofInt]

/-- Rank-one bound: `|c| · Π_l B_l` if `|E l p| ≤ B_l`. -/
lemma boundTree_rank1_le (E : ℕ → Fin 24 → ℤ) (c : ℤ) (B0 B1 B2 B3 : ℕ) (h0 : ∀ p, (E 0 p).natAbs ≤ B0)
    (h1 : ∀ p, (E 1 p).natAbs ≤ B1) (h2 : ∀ p, (E 2 p).natAbs ≤ B2) (h3 : ∀ p, (E 3 p).natAbs ≤ B3) :
    boundTree (rank1Spec E c) rank1Tree ≤ c.natAbs * (B0 * B1 * B2 * B3) := by
  rw [boundTree_rank1]
  have := Nat.mul_le_mul (rowAbs_rank1_le E c 3 B3 h3) (Nat.mul_le_mul (rowAbs_rank1_le E c 2 B2 h2)
    (Nat.mul_le_mul (rowAbs_rank1_le E c 1 B1 h1) (Nat.mul_le_mul (rowAbs_rank1_le E c 0 B0 h0) (le_refl c.natAbs))))
  calc _ ≤ B3 * (B2 * (B1 * (B0 * c.natAbs))) := this
    _ = c.natAbs * (B0 * B1 * B2 * B3) := by ring

/-! ### Equality local maps -/

/-- Largest `|J|` entry over all modules. -/
def maxJall (C : CertD) : ℕ := maxNat (C.mods.map fun md => maxAbsI md.J)

/-- Crude bound on every equality local map value at leg dimension `n`: `(n^8 + 1024) · max|J|²`. -/
def eqB (C : CertD) (n : ℕ) : ℕ := (n ^ 8 + 1024) * maxJall C ^ 2

lemma maxAbsI_mods_le (C : CertD) (i : ℕ) : maxAbsI (C.mods.getD i default).J ≤ maxJall C := by
  rcases Nat.lt_or_ge i C.mods.length with hi | hi
  · exact le_maxNat (List.mem_map.2 ⟨_, getD_mem_of_lt _ _ _ hi, rfl⟩)
  · rw [getD_ge _ _ _ hi, show maxAbsI (default : ModD).J = 0 from rfl]; exact Nat.zero_le _

lemma abs_JJ_le (J : List (List ℤ)) (a b μ ν : ℕ) :
    |(J.getD a []).getD μ 0 * (J.getD b []).getD ν 0| ≤ ((maxAbsI J ^ 2 : ℕ) : ℤ) := by
  rw [abs_mul]; push_cast
  calc |(J.getD a []).getD μ 0| * |(J.getD b []).getD ν 0| ≤ (maxAbsI J : ℤ) * maxAbsI J :=
        mul_le_mul (abs_getD_le _ _ _) (abs_getD_le _ _ _) (abs_nonneg _) (by positivity)
    _ = (maxAbsI J : ℤ) ^ 2 := by ring

lemma abs_delFast_le (J : List (List ℤ)) (slot : ℕ) (order : List ℕ) (n : ℕ) [NeZero n] (p : Fin 24) (μ ν : ℕ) :
    |delFast J slot order n p μ ν| ≤ ((n ^ 4 * maxAbsI J ^ 2 : ℕ) : ℤ) := by
  unfold delFast
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ k ∈ range (n ^ 4), |(if unflat n 4 k (sF slot) = unflat n 4 k (pf p (sF slot)) then
        (J.getD (flat (unflat n 4 k ∘ oF order)) []).getD μ 0 *
          (J.getD (flat (unflat n 4 k ∘ pf p ∘ oF order)) []).getD ν 0 else 0)|
      ≤ ∑ k ∈ range (n ^ 4), ((maxAbsI J ^ 2 : ℕ) : ℤ) := Finset.sum_le_sum fun k _ => by
        split_ifs
        · exact abs_JJ_le _ _ _ _ _
        · simp
    _ = ((n ^ 4 * maxAbsI J ^ 2 : ℕ) : ℤ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

lemma trE_bounds (slot : ℕ) (order : List ℕ) (n : ℕ) (p : Fin 24) (x y : Fin 3 → Fin n) :
    0 ≤ trE slot order n p x y ∧ trE slot order n p x y ≤ n := by
  unfold trE
  constructor
  · exact Finset.sum_nonneg fun z _ => by split_ifs <;> norm_num
  · calc ∑ z : Fin n, (if insAt slot order x z = insAt slot order y z ∘ pinvf p then (1 : ℤ) else 0)
        ≤ ∑ _z : Fin n, (1 : ℤ) := Finset.sum_le_sum fun z _ => by split_ifs <;> norm_num
      _ = n := by simp

lemma abs_delB_le (J : List (List ℤ)) (slot : ℕ) (order : List ℕ) (n : ℕ) [NeZero n] (p : Fin 24) (μ ν : ℕ) :
    |delB J slot order n p μ ν| ≤ ((n ^ 3 * n ^ 3 * (n * maxAbsI J ^ 2) : ℕ) : ℤ) := by
  unfold delB
  have hterm : ∀ xi yi, |(J.getD xi []).getD μ 0 * trE slot order n p (unflat n 3 xi) (unflat n 3 yi) *
      (J.getD yi []).getD ν 0| ≤ ((n * maxAbsI J ^ 2 : ℕ) : ℤ) := by
    intro xi yi
    obtain ⟨h0, h1⟩ := trE_bounds slot order n p (unflat n 3 xi) (unflat n 3 yi)
    rw [abs_mul, abs_mul, abs_of_nonneg h0]
    push_cast
    calc |(J.getD xi []).getD μ 0| * trE slot order n p (unflat n 3 xi) (unflat n 3 yi) * |(J.getD yi []).getD ν 0|
        ≤ (maxAbsI J : ℤ) * n * maxAbsI J :=
          mul_le_mul (mul_le_mul (abs_getD_le _ _ _) h1 h0 (by positivity)) (abs_getD_le _ _ _) (abs_nonneg _)
            (by positivity)
      _ = n * (maxAbsI J : ℤ) ^ 2 := by ring
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ xi ∈ range (n ^ 3), |∑ yi ∈ range (n ^ 3), (J.getD xi []).getD μ 0 *
        trE slot order n p (unflat n 3 xi) (unflat n 3 yi) * (J.getD yi []).getD ν 0|
      ≤ ∑ xi ∈ range (n ^ 3), ∑ yi ∈ range (n ^ 3), ((n * maxAbsI J ^ 2 : ℕ) : ℤ) :=
        Finset.sum_le_sum fun xi _ => le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun yi _ => hterm xi yi)
    _ = ((n ^ 3 * n ^ 3 * (n * maxAbsI J ^ 2) : ℕ) : ℤ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

lemma abs_stiefE_le (slot : ℕ) (p : Fin 24) (i j : Fin 4 → Fin 2) : |stiefE slot p i j| ≤ 4 := by
  unfold stiefE
  have h1 : |(2 : ℤ) * (if i = j ∘ pinvf p then 1 else 0)| ≤ 2 := by split_ifs <;> norm_num
  have h2 : |(if i (Fin.ofNat 4 slot) = j (Fin.ofNat 4 slot) then
      ∑ z : Fin 2, (if insAt slot (natOrder slot) (restr slot i) z =
        insAt slot (natOrder slot) (restr slot j) z ∘ pinvf p then (1 : ℤ) else 0) else 0)| ≤ 2 := by
    split_ifs
    · rw [Fin.sum_univ_two]
      split_ifs <;> norm_num
    · simp
  calc _ ≤ _ := abs_sub _ _
    _ ≤ 2 + 2 := add_le_add h1 h2
    _ = 4 := by norm_num

lemma abs_stiefF_le (J : List (List ℤ)) (slot : ℕ) (p : Fin 24) (μ ν : ℕ) :
    |stiefF J slot p μ ν| ≤ ((16 * 16 * (4 * maxAbsI J ^ 2) : ℕ) : ℤ) := by
  unfold stiefF
  have hterm : ∀ ii jj, |(J.getD ii []).getD μ 0 * stiefE slot p (unflat 2 4 ii) (unflat 2 4 jj) *
      (J.getD jj []).getD ν 0| ≤ ((4 * maxAbsI J ^ 2 : ℕ) : ℤ) := by
    intro ii jj
    rw [abs_mul, abs_mul]
    push_cast
    calc |(J.getD ii []).getD μ 0| * |stiefE slot p (unflat 2 4 ii) (unflat 2 4 jj)| * |(J.getD jj []).getD ν 0|
        ≤ (maxAbsI J : ℤ) * 4 * maxAbsI J :=
          mul_le_mul (mul_le_mul (abs_getD_le _ _ _) (abs_stiefE_le _ _ _ _) (abs_nonneg _) (by positivity))
            (abs_getD_le _ _ _) (abs_nonneg _) (by positivity)
      _ = 4 * (maxAbsI J : ℤ) ^ 2 := by ring
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ ii ∈ range (2 ^ 4), |∑ jj ∈ range (2 ^ 4), (J.getD ii []).getD μ 0 *
        stiefE slot p (unflat 2 4 ii) (unflat 2 4 jj) * (J.getD jj []).getD ν 0|
      ≤ ∑ ii ∈ range (2 ^ 4), ∑ jj ∈ range (2 ^ 4), ((4 * maxAbsI J ^ 2 : ℕ) : ℤ) :=
        Finset.sum_le_sum fun ii _ => le_trans (Finset.abs_sum_le_sum_abs _ _)
          (Finset.sum_le_sum fun jj _ => hterm ii jj)
    _ = ((16 * 16 * (4 * maxAbsI J ^ 2) : ℕ) : ℤ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- Every equality local map value is at most `eqB C n`. -/
lemma eqLocF_le (C : CertD) (sp : EqSpecD) (n : ℕ) (p : Fin 24) (o : ℕ) :
    |eqLocF C sp n p o| ≤ (eqB C n : ℤ) := by
  have hmd := maxAbsI_mods_le C (sp.mkeys.getD (C.eqDecode sp.mkeys o).1 0)
  have hB : ∀ X : ℕ, X ≤ (n ^ 8 + 1024) * maxAbsI (C.mods.getD (sp.mkeys.getD (C.eqDecode sp.mkeys o).1 0)
      default).J ^ 2 → (X : ℤ) ≤ eqB C n := by
    intro X hX
    have : (n ^ 8 + 1024) * maxAbsI (C.mods.getD (sp.mkeys.getD (C.eqDecode sp.mkeys o).1 0) default).J ^ 2 ≤
        eqB C n := Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left hmd 2)
    exact_mod_cast le_trans hX this
  unfold eqLocF
  dsimp only
  generalize C.eqDecode sp.mkeys o = dec at hB hmd ⊢
  generalize C.mods.getD (sp.mkeys.getD dec.1 0) default = md at hB hmd ⊢
  have hn8 : n ^ 4 ≤ n ^ 8 + 1024 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · exact le_trans (Nat.pow_le_pow_right h (by norm_num)) (Nat.le_add_right _ _)
  have hn7 : n ^ 3 * n ^ 3 * n ≤ n ^ 8 + 1024 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · calc n ^ 3 * n ^ 3 * n = n ^ 7 := by ring
        _ ≤ n ^ 8 := Nat.pow_le_pow_right h (by norm_num)
        _ ≤ n ^ 8 + 1024 := Nat.le_add_right _ _
  split_ifs with hμ hν hk hn hso
  · simp
  · have : NeZero n := ⟨hn⟩
    refine le_trans (abs_delFast_le md.J sp.slot sp.order n p dec.2.1 dec.2.2) (hB _ ?_)
    exact Nat.mul_le_mul hn8 le_rfl
  · have : NeZero n := ⟨hn⟩
    refine le_trans (abs_delB_le md.J sp.slot sp.order n p dec.2.1 dec.2.2) (hB _ ?_)
    calc n ^ 3 * n ^ 3 * (n * maxAbsI md.J ^ 2) = (n ^ 3 * n ^ 3 * n) * maxAbsI md.J ^ 2 := by ring
      _ ≤ (n ^ 8 + 1024) * maxAbsI md.J ^ 2 := Nat.mul_le_mul hn7 le_rfl
  · refine le_trans (abs_stiefF_le md.J sp.slot p dec.2.1 dec.2.2) (hB _ ?_)
    calc 16 * 16 * (4 * maxAbsI md.J ^ 2) = 1024 * maxAbsI md.J ^ 2 := by ring
      _ ≤ (n ^ 8 + 1024) * maxAbsI md.J ^ 2 := Nat.mul_le_mul (Nat.le_add_left _ _) le_rfl
  · simp
  · simp

/-! ### The crude bound -/

/-- Largest block size. -/
def nbMax (C : CertD) : ℕ := maxNat (C.Z.map fun b => b.n)
/-- Largest module dimension. -/
def dimMax (C : CertD) : ℕ := maxNat (C.mods.map fun md => md.dim)
/-- Largest local dimension. -/
def nMax (C : CertD) : ℕ := maxNat (C.mods.map fun md => md.n)
/-- Largest `|W|` entry over all types. -/
def maxWall (C : CertD) : ℕ := maxNat (C.types.map fun t => maxAbsI t.W)
/-- Largest `|Zq|` bound over all blocks. -/
def zqBmax (C : CertD) (zmul : ℕ) : ℕ := maxNat (C.Z.map fun b => zqB b zmul)
/-- Largest `|z p|`. -/
def tabMax (z : Fin 24 → ℤ) : ℕ := maxNat ((List.finRange 24).map fun p => (z p).natAbs)

/-- Number of equality-multiplier entries of family `f` (= number of its rank-one equality parts). -/
def eqCount (C : CertD) (f : ℕ) : ℕ :=
  (C.eqs.flatMap fun g => g.parts.flatMap fun P => if P.fam = f then g.lam else []).length

/-- Largest coefficient `|sign · den3 · λ|` of the rank-one equality parts of family `f`. -/
def eqCoefMax (C : CertD) (f : ℕ) : ℕ :=
  maxNat (C.eqs.flatMap fun g => g.parts.flatMap fun P =>
    if P.fam = f then g.lam.map (fun ol => (-(P.sign) * (den3 C.d : ℤ) * ol.2).natAbs) else [])

/-- **Term count**: per rule-group item `nb² · (dim² · n^8)^4` (maxima), `1` for the objective (family 0), `1` per
equality-multiplier entry. -/
def crudeN (C : CertD) (f : ℕ) (gs : List GrpF) : ℕ :=
  (gs.map fun G => (itemsOf G.tree).length).sum *
      (nbMax C * nbMax C * (dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4)) ^ 4) +
    (if f = 0 then 1 else 0) + eqCount C f

/-- **Largest coefficient**: `max(den3 · max|Zq|, 2 Lden, max|sign · den3 · λ|)`. -/
def crudeK (C : CertD) (zmul f : ℕ) : ℕ := max (den3 C.d * zqBmax C zmul) (max (2 * C.Lden) (eqCoefMax C f))

/-- **Largest value**: `max(max|W|² · max|J|^8, max|zs|³ · max|za|, eqB(d)³ · eqB(2))`. -/
def crudeV (C : CertD) (zs za : Fin 24 → ℤ) : ℕ :=
  max (maxWall C ^ 2 * maxJall C ^ 8) (max (tabMax zs ^ 3 * tabMax za) (eqB C C.d ^ 3 * eqB C 2))

/-- **The crude bound** `term count × largest coefficient × largest value`. -/
def crudeB (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) : ℕ :=
  crudeN C f gs * crudeK C zmul f * crudeV C zs za

lemma le_tabMax (z : Fin 24 → ℤ) (p : Fin 24) : (z p).natAbs ≤ tabMax z :=
  le_maxNat (List.mem_map.2 ⟨p, List.mem_finRange p, rfl⟩)

lemma getD_le_maxNat {α : Type} [Inhabited α] (L : List α) (g : α → ℕ) (hd : g default = 0) (i : ℕ) :
    g (L.getD i default) ≤ maxNat (L.map g) := by
  rcases Nat.lt_or_ge i L.length with hi | hi
  · exact le_maxNat (List.mem_map.2 ⟨_, getD_mem_of_lt _ _ _ hi, rfl⟩)
  · rw [getD_ge _ _ _ hi, hd]; exact Nat.zero_le _

lemma itemB_le (C : CertD) (zmul : ℕ) (it : ℕ × ℕ × ℕ) :
    itemB C zmul (-(den3 C.d : ℤ)) it ≤ nbMax C * nbMax C * (den3 C.d * zqBmax C zmul) * maxWall C ^ 2 := by
  unfold itemB
  have hn := getD_le_maxNat C.Z (fun b => b.n) rfl (C.types.getD it.1 default).zi
  have hz0 : zqB (default : NPT.Cert.PBlock) zmul = 0 := by
    show maxAbsI (default : NPT.Cert.PBlock).zrows * zmul + 2 * maxNat ((default : NPT.Cert.PBlock).uent.map
      fun e => e.2.2.natAbs) = 0
    rw [show maxAbsI (default : NPT.Cert.PBlock).zrows = 0 from rfl,
      show maxNat ((default : NPT.Cert.PBlock).uent.map fun e => e.2.2.natAbs) = 0 from rfl]
    simp
  have hz := getD_le_maxNat C.Z (fun b => zqB b zmul) hz0 (C.types.getD it.1 default).zi
  have hw := getD_le_maxNat C.types (fun t => maxAbsI t.W) rfl it.1
  simp only [Int.natAbs_neg, Int.natAbs_natCast] at *
  unfold nbMax zqBmax maxWall
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hn hn) (Nat.mul_le_mul le_rfl hz)) (Nat.pow_le_pow_left hw 2)

lemma rowB_le (C : CertD) (md : ModD) (hmd : md ∈ C.mods) :
    rowB md ≤ dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4 * maxJall C ^ 2) := by
  have hd : md.dim ≤ dimMax C := le_maxNat (List.mem_map.2 ⟨md, hmd, rfl⟩)
  have hn : md.n ≤ nMax C := le_maxNat (List.mem_map.2 ⟨md, hmd, rfl⟩)
  have hj : maxAbsI md.J ≤ maxJall C := le_maxNat (List.mem_map.2 ⟨md, hmd, rfl⟩)
  unfold rowB
  have h4 := Nat.pow_le_pow_left hn 4
  exact Nat.mul_le_mul (Nat.mul_le_mul hd hd) (Nat.mul_le_mul (Nat.mul_le_mul h4 h4) (Nat.pow_le_pow_left hj 2))

/-- The rule-group parts. -/
lemma groups_bound_le (C : CertD) (zmul : ℕ) (gs : List GrpF) :
    (gs.map fun G => boundTree (ruleSpecF C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos) G.tree).sum ≤
      (gs.map fun G => (itemsOf G.tree).length).sum *
        (nbMax C * nbMax C * (dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4)) ^ 4) *
        (den3 C.d * zqBmax C zmul) * (maxWall C ^ 2 * maxJall C ^ 8) := by
  set R := dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4 * maxJall C ^ 2)
  set IB := nbMax C * nbMax C * (den3 C.d * zqBmax C zmul) * maxWall C ^ 2
  have hG : ∀ G ∈ gs, boundTree (ruleSpecF C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos) G.tree ≤
      (itemsOf G.tree).length * (R ^ 4 * IB) := by
    intro G _
    refine le_trans (boundTree_ruleSpecF_le C zmul _ G.kpos G.lpos R (fun md hmd => rowB_le C md hmd) G.tree) ?_
    have : ((itemsOf G.tree).map (itemB C zmul (-(den3 C.d : ℤ)))).sum ≤ (itemsOf G.tree).length * IB := by
      have := List.sum_le_length_nsmul ((itemsOf G.tree).map (itemB C zmul (-(den3 C.d : ℤ)))) IB
        (fun x hx => by obtain ⟨it, -, rfl⟩ := List.mem_map.1 hx; exact itemB_le C zmul it)
      simpa using this
    calc R ^ 4 * ((itemsOf G.tree).map (itemB C zmul (-(den3 C.d : ℤ)))).sum ≤ R ^ 4 * ((itemsOf G.tree).length * IB) :=
          Nat.mul_le_mul le_rfl this
      _ = (itemsOf G.tree).length * (R ^ 4 * IB) := by ring
  calc (gs.map fun G => boundTree (ruleSpecF C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos) G.tree).sum
      ≤ (gs.map fun G => (itemsOf G.tree).length * (R ^ 4 * IB)).sum := List.sum_le_sum fun G hG' => hG G hG'
    _ = (gs.map fun G => (itemsOf G.tree).length).sum * (R ^ 4 * IB) := by rw [List.sum_map_mul_right]
    _ = _ := by simp only [R, IB]; ring

lemma eqParts_length (C : CertD) (f : ℕ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) :
    (eqPartsF C f eqT).length = eqCount C f := by
  unfold eqPartsF eqCount
  simp only [List.length_flatMap]
  congr 1
  refine List.map_congr_left fun g _ => ?_
  congr 1
  refine List.map_congr_left fun P _ => ?_
  split_ifs <;> simp

/-- The equality parts. -/
lemma eq_bound_le (C : CertD) (f : ℕ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heqT : ∀ sp n p o, |eqT sp n p o| ≤ (eqB C n : ℤ)) :
    ((eqPartsF C f eqT).map fun P => boundTree P.S P.tree).sum ≤
      eqCount C f * (eqCoefMax C f * (eqB C C.d ^ 3 * eqB C 2)) := by
  rw [← eqParts_length C f eqT]
  have := List.sum_le_length_nsmul ((eqPartsF C f eqT).map fun P => boundTree P.S P.tree)
    (eqCoefMax C f * (eqB C C.d ^ 3 * eqB C 2)) ?_
  · simpa using this
  intro x hx
  obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
  unfold eqPartsF at hP
  simp only [List.mem_flatMap] at hP
  obtain ⟨g, hg, P', hP', hPin⟩ := hP
  split_ifs at hPin with hf
  · obtain ⟨ol, hol, rfl⟩ := List.mem_map.1 hPin
    have hE : ∀ l < 4, ∀ p, (eqT (P'.specs.getD l default) (nfN C.d l) p (ol.1.getD l 0)).natAbs ≤ eqB C (nfN C.d l) := by
      intro l _ p
      have := heqT (P'.specs.getD l default) (nfN C.d l) p (ol.1.getD l 0)
      rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
    refine le_trans (boundTree_rank1_le _ _ _ _ _ _ (hE 0 (by norm_num)) (hE 1 (by norm_num)) (hE 2 (by norm_num))
      (hE 3 (by norm_num))) ?_
    have hc : (-(P'.sign) * (den3 C.d : ℤ) * ol.2).natAbs ≤ eqCoefMax C f := by
      unfold eqCoefMax
      refine le_maxNat ?_
      simp only [List.mem_flatMap]
      exact ⟨g, hg, P', hP', by rw [ite_eq_left hf]; exact List.mem_map.2 ⟨ol, hol, rfl⟩⟩
    have hn : nfN C.d 0 = C.d ∧ nfN C.d 1 = C.d ∧ nfN C.d 2 = C.d ∧ nfN C.d 3 = 2 := by simp [nfN]
    rw [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]
    calc (-(P'.sign) * (den3 C.d : ℤ) * ol.2).natAbs * (eqB C C.d * eqB C C.d * eqB C C.d * eqB C 2)
        ≤ eqCoefMax C f * (eqB C C.d * eqB C C.d * eqB C C.d * eqB C 2) := Nat.mul_le_mul hc le_rfl
      _ = eqCoefMax C f * (eqB C C.d ^ 3 * eqB C 2) := by ring
  · simp at hPin

/-- **Crude a-priori bound** on the word values of family `f`: `|partsF| ≤ crudeN · crudeK · crudeV`
(term count × largest coefficient × largest value), for every `eqT` bounded by `eqB` (e.g. `eqLocF C`). -/
theorem partsF_le_crudeB (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (heqT : ∀ sp n p o, |eqT sp n p o| ≤ (eqB C n : ℤ))
    (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (famParts C zmul f gs zs za eqT) w0 w1 w2 w3| ≤ (crudeB C zmul f gs zs za : ℤ) := by
  refine le_trans (partsF_abs _ (famParts_rows C zmul f gs zs za eqT) w0 w1 w2 w3 hw0 hw1 hw2 hw3) ?_
  have hK1 : den3 C.d * zqBmax C zmul ≤ crudeK C zmul f := le_max_left _ _
  have hK2 : 2 * C.Lden ≤ crudeK C zmul f := le_trans (le_max_left _ _) (le_max_right _ _)
  have hK3 : eqCoefMax C f ≤ crudeK C zmul f := le_trans (le_max_right _ _) (le_max_right _ _)
  have hV1 : maxWall C ^ 2 * maxJall C ^ 8 ≤ crudeV C zs za := le_max_left _ _
  have hV2 : tabMax zs ^ 3 * tabMax za ≤ crudeV C zs za := le_trans (le_max_left _ _) (le_max_right _ _)
  have hV3 : eqB C C.d ^ 3 * eqB C 2 ≤ crudeV C zs za := le_trans (le_max_right _ _) (le_max_right _ _)
  set K := crudeK C zmul f
  set V := crudeV C zs za
  set NG := (gs.map fun G => (itemsOf G.tree).length).sum *
    (nbMax C * nbMax C * (dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4)) ^ 4)
  -- the three kinds of parts
  have hgr := groups_bound_le C zmul gs
  have hgr' : (gs.map fun G => boundTree (ruleSpecF C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos) G.tree).sum ≤ NG * K * V :=
    le_trans hgr (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hK1) hV1)
  have hobj : boundTree (rank1Spec (objE zs za) (2 * C.Lden)) rank1Tree ≤ K * V := by
    have hz : ∀ l < 3, ∀ p, (objE zs za l p).natAbs ≤ tabMax zs := by
      intro l hl p; simp only [objE, ite_eq_left hl]; exact le_tabMax zs p
    have ha : ∀ p, (objE zs za 3 p).natAbs ≤ tabMax za := by
      intro p; simp only [objE]; exact le_tabMax za p
    refine le_trans (boundTree_rank1_le _ _ _ _ _ _ (hz 0 (by norm_num)) (hz 1 (by norm_num)) (hz 2 (by norm_num)) ha) ?_
    have hc : ((2 * C.Lden : ℕ) : ℤ).natAbs = 2 * C.Lden := Int.natAbs_natCast _
    push_cast at hc
    rw [show ((2 : ℤ) * (C.Lden : ℤ)).natAbs = 2 * C.Lden by simpa using hc]
    calc 2 * C.Lden * (tabMax zs * tabMax zs * tabMax zs * tabMax za) = 2 * C.Lden * (tabMax zs ^ 3 * tabMax za) := by ring
      _ ≤ K * V := Nat.mul_le_mul hK2 hV2
  have heq := eq_bound_le C f eqT heqT
  have heq' : ((eqPartsF C f eqT).map fun P => boundTree P.S P.tree).sum ≤ eqCount C f * (K * V) :=
    le_trans heq (Nat.mul_le_mul le_rfl (Nat.mul_le_mul hK3 hV3))
  -- assemble
  have hnat : partsBound (famParts C zmul f gs zs za eqT) ≤ crudeB C zmul f gs zs za := by
    unfold partsBound famParts
    simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
    have hsum : (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []).map (fun P => boundTree P.S P.tree) =
        if f = 0 then [boundTree (rank1Spec (objE zs za) (2 * C.Lden)) rank1Tree] else [] := by
      split_ifs <;> rfl
    rw [hsum]
    have hobj' : (if f = 0 then [boundTree (rank1Spec (objE zs za) (2 * C.Lden)) rank1Tree] else []).sum ≤
        (if f = 0 then 1 else 0) * (K * V) := by
      split_ifs <;> simp [hobj]
    have htot : NG * K * V + (if f = 0 then 1 else 0) * (K * V) + eqCount C f * (K * V) =
        crudeB C zmul f gs zs za := by
      unfold crudeB crudeN; ring
    rw [← htot]
    exact add_le_add (add_le_add hgr' hobj') heq'
  exact_mod_cast hnat

/-- The crude bound for the certificate's own equality maps (`eqT = eqLocF C`). -/
theorem partsF_le_crudeB_eqLocF (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (famParts C zmul f gs zs za (eqLocF C)) w0 w1 w2 w3| ≤ (crudeB C zmul f gs zs za : ℤ) :=
  partsF_le_crudeB C zmul f gs zs za (eqLocF C) (eqLocF_le C) w0 w1 w2 w3 hw0 hw1 hw2 hw3

/-- `crudeB` with the block maximum `zqBmax C zmul` replaced by an upper bound `Z`: the block scan (the expensive
part of `crudeB`) can then be checked once (`zqBmax C zmul ≤ Z`) and each family's `crudeBZ` separately. -/
def crudeBZ (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) (Z : ℕ) : ℕ :=
  crudeN C f gs * max (den3 C.d * Z) (max (2 * C.Lden) (eqCoefMax C f)) * crudeV C zs za

lemma crudeB_le_crudeBZ (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) (Z : ℕ)
    (hZ : zqBmax C zmul ≤ Z) : crudeB C zmul f gs zs za ≤ crudeBZ C f gs zs za Z := by
  unfold crudeB crudeBZ crudeK
  exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (max_le_max (Nat.mul_le_mul le_rfl hZ) le_rfl)) le_rfl

/-- `partsF_le_crudeB_eqLocF` with the block maximum replaced by an upper bound `Z`. -/
theorem partsF_le_crudeBZ_eqLocF (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) (Z : ℕ)
    (hZ : zqBmax C zmul ≤ Z) (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (famParts C zmul f gs zs za (eqLocF C)) w0 w1 w2 w3| ≤ (crudeBZ C f gs zs za Z : ℤ) :=
  le_trans (partsF_le_crudeB_eqLocF C zmul f gs zs za w0 w1 w2 w3 hw0 hw1 hw2 hw3)
    (by exact_mod_cast crudeB_le_crudeBZ C zmul f gs zs za Z hZ)

end

end NPT.Cert.Ident
