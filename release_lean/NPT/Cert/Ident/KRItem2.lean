/-
NPT.Cert.Ident.KRItem2 — item rows with sparse `W` rows. Same leaf rows as `KRItem` (`leafRowsC2_gv`,
`leafRowsC2_LRShape`), but each `W` row is first put in sparse form `(gap, value)` (`spR`), and every dot product with a
`W` row walks only its nonzero entries (`dotSpR`): `Y = Zq · Wsᵀ` and the entries `⟨W_r[μ], Y[ν]⟩` cost `O(nnz)` products
instead of `O(n)`.
-/
import NPT.Cert.Ident.KRGlue

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident

namespace NPT.Cert.KR

/-- One more zero before the first entry of a sparse row (trailing zeros are dropped). -/
noncomputable def bumpR (sp : List (ℕ × SInt)) : List (ℕ × SInt) :=
  @List.casesOn (ℕ × SInt) (fun _ => List (ℕ × SInt)) sp []
    (fun p rest => @Prod.casesOn ℕ SInt (fun _ => List (ℕ × SInt)) p (fun g v => (Nat.succ g, v) :: rest))

/-- Sparse form of a row: one `(gap, value)` per nonzero entry, `gap` = number of zeros skipped before it. -/
noncomputable def spR (row : List SInt) : List (ℕ × SInt) :=
  @List.rec SInt (fun _ => List (ℕ × SInt)) []
    (fun x _ acc => @Bool.rec (fun _ => List (ℕ × SInt)) ((0, x) :: acc) (bumpR acc)
      (@SInt.casesOn (fun _ => Bool) x fun _ m => Nat.beq m 0))
    row

/-- `Σ_k v_k · x[pos_k]` along a sparse row. -/
noncomputable def dotSpR (x : List SInt) (sp : List (ℕ × SInt)) : SInt :=
  @List.rec (ℕ × SInt) (fun _ => List SInt → SInt) (fun _ => ⟨false, 0⟩)
    (fun p _ ih => fun x => @Prod.casesOn ℕ SInt (fun _ => SInt) p fun g v =>
      @List.casesOn SInt (fun _ => SInt) (dropR g x) ⟨false, 0⟩ (fun h t => addS (mulS h v) (ih t)))
    sp x

/-- Row `(μ0, ν0)` of an item tensor, `W_r` rows sparse. -/
noncomputable def rowR2 (cS : SInt) (wr0 : List (List (List (List (ℕ × SInt))))) (y0 : List (List (List (List SInt)))) :
    List SInt :=
  pairsR (fun w1 y1 acc1 => pairsR (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotSpR y3 w3) :: acc3)
    w2 y2 acc2) w1 y1 acc1) wr0 y0 []

/-- All rows `i0 = μ0 d0 + ν0` of an item tensor, `W_r` rows sparse. -/
noncomputable def itemRowsR2 (cS : SInt) (WrN : List (List (List (List (List (ℕ × SInt))))))
    (YN : List (List (List (List (List SInt))))) : List (List SInt) :=
  foldrR (fun wr0 acc => foldrR (fun y0 acc' => rowR2 cS wr0 y0 :: acc') acc YN) [] WrN

/-- The leaf rows of one item `(t, r, s)` with sparse `W` rows (recursors only). -/
noncomputable def itemRowsC2 (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) : List (List SInt) :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let nn := Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3)
  let Zq := mapR (fun row => mapR ofIntS (takePadR b.n 0 row)) (takePadR b.n [] b.zrows)
  let Wr := mapR (fun row => spR (mapR ofIntS (takePadR b.n 0 row))) (takePadR nn [] (dropR (Nat.mul it.2.1 nn) t.W))
  let Ws := mapR (fun row => spR (mapR ofIntS (takePadR b.n 0 row))) (takePadR nn [] (dropR (Nat.mul it.2.2 nn) t.W))
  let Y := mapR (fun ws => mapR (fun zrow => dotSpR zrow ws) Zq) Ws
  itemRowsR2 (ofIntS coef) (nest4R d0 d1 d2 d3 Wr) (nest4R d0 d1 d2 d3 Y)

/-- The leaf rows of a leaf: the row-wise sum of its items' rows. -/
noncomputable def leafRowsC2 (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ)) :
    List (List SInt) :=
  foldrR (fun it acc => addRowsR (itemRowsC2 C coef d0 d1 d2 d3 it) acc) [] items

namespace KI2

open KI

/-! ### Sparse dot products -/

lemma dotSpR_nil_sp (x : List SInt) : dotSpR x [] = ⟨false, 0⟩ := rfl

lemma dotSpR_nil_x (sp : List (ℕ × SInt)) : (dotSpR [] sp).val = 0 := by
  cases sp with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨g, v⟩
    cases g <;> rfl

lemma dotSpR_bumpR (sp : List (ℕ × SInt)) (x : List SInt) : (dotSpR x (bumpR sp)).val = (dotSpR x.tail sp).val := by
  cases sp with
  | nil =>
    show (dotSpR x []).val = (dotSpR x.tail []).val
    rfl
  | cons p rest =>
    rcases p with ⟨g, v⟩
    cases x with
    | nil => rw [List.tail_nil, dotSpR_nil_x]; exact (dotSpR_nil_x _).symm
    | cons h t => rfl

lemma dotR_val_cons (y : SInt) (w : List SInt) (h : SInt) (t : List SInt) :
    (dotR (y :: w) (h :: t)).val = y.val * h.val + (dotR w t).val := by
  show (addS (mulS y h) (dotR w t)).val = _
  rw [addS_eq, mulS_eq, SInt.val_add, SInt.val_mul]

lemma dotR_val_nil_right (w : List SInt) : (dotR w []).val = 0 := by
  cases w <;> rfl

/-- **Sparse dot product.** Walking `x` along the nonzero entries of `w` gives `⟨w, x⟩`. -/
lemma dotSpR_spR : ∀ (w x : List SInt), (dotSpR x (spR w)).val = (dotR w x).val
  | [], x => by cases x <;> rfl
  | y :: w, x => by
    rcases y with ⟨ys, ym⟩
    have hsp : spR (⟨ys, ym⟩ :: w) = @Bool.rec (fun _ => List (ℕ × SInt)) ((0, ⟨ys, ym⟩) :: spR w) (bumpR (spR w))
        (Nat.beq ym 0) := rfl
    rw [hsp]
    cases hb : Nat.beq ym 0 with
    | true =>
      have hm : ym = 0 := Nat.eq_of_beq_eq_true hb
      subst hm
      show (dotSpR x (bumpR (spR w))).val = _
      rw [dotSpR_bumpR]
      cases x with
      | nil => rw [List.tail_nil, dotSpR_nil_x, dotR_val_nil_right]
      | cons h t =>
        rw [List.tail_cons, dotSpR_spR w t, dotR_val_cons]
        cases ys <;> simp [SInt.val]
    | false =>
      show (dotSpR x ((0, ⟨ys, ym⟩) :: spR w)).val = _
      cases x with
      | nil => rw [dotSpR_nil_x, dotR_val_nil_right]
      | cons h t =>
        show (addS (mulS h ⟨ys, ym⟩) (dotSpR t (spR w))).val = _
        rw [addS_eq, mulS_eq, SInt.val_add, SInt.val_mul, dotSpR_spR w t, dotR_val_cons, mul_comm]

/-- The value of a dot product depends only on the entries' values. -/
lemma dotR_val_eq (w : List SInt) : ∀ (x x' : List SInt), x.length = x'.length →
    (∀ i < x.length, (x.getD i SInt.zero).val = (x'.getD i SInt.zero).val) → (dotR w x).val = (dotR w x').val := by
  intro x x' hl hv
  rw [dotR_eq, dotR_eq, dotS_val, dotS_val, ← hl]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < x.length := lt_of_lt_of_le (Finset.mem_range.1 hi) (min_le_right _ _)
  rw [hv i hi']

/-- The value of a dot product is symmetric. -/
lemma dotR_val_comm (u v : List SInt) : (dotR u v).val = (dotR v u).val := by
  rw [dotR_eq, dotR_eq, dotS_val, dotS_val, min_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ### Index form -/

/-- Row `v` of `Y = Z · Sᵀ` computed with the sparse form of `S`. -/
noncomputable def yRow2 (Z W : List (List Int)) (n k v : ℕ) : List SInt :=
  (List.range n).map fun a => dotSpR (zRow Z n a) (spR (wRow W n k v))

/-- The leaf rows in index form, `W_r` rows sparse. -/
noncomputable def rowsF2 (W Z : List (List Int)) (n kr ks : ℕ) (cS : SInt) (d0 d1 d2 d3 : ℕ) : List (List SInt) :=
  (List.range d0).flatMap fun μ0 => (List.range d0).map fun ν0 =>
    (List.range d1).flatMap fun μ1 => (List.range d1).flatMap fun ν1 =>
    (List.range d2).flatMap fun μ2 => (List.range d2).flatMap fun ν2 =>
    (List.range d3).flatMap fun μ3 => (List.range d3).map fun ν3 =>
      mulS cS (dotSpR (yRow2 Z W n ks (mr4 d0 d1 d2 d3 ν0 ν1 ν2 ν3)) (spR (wRow W n kr (mr4 d0 d1 d2 d3 μ0 μ1 μ2 μ3))))

lemma spPadRows_eq (n m : ℕ) (L : List (List Int)) :
    mapR (fun row => spR (mapR ofIntS (takePadR m 0 row))) (takePadR n [] L) =
      (List.range n).map fun v => spR ((List.range m).map fun c => ofIntS ((L.getD v []).getD c 0)) := by
  rw [takePadR_eq, mapR_eq, List.map_map]
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply]
  rw [mapR_eq, takePadR_eq, List.map_map]
  rfl

lemma rowR2_eq (cS : SInt) (wr0 : List (List (List (List (ℕ × SInt))))) (y0 : List (List (List (List SInt)))) :
    rowR2 cS wr0 y0 = wr0.flatMap fun w1 => y0.flatMap fun y1 => w1.flatMap fun w2 => y1.flatMap fun y2 =>
      w2.flatMap fun w3 => y2.flatMap fun y3 => [mulS cS (dotSpR y3 w3)] := by
  unfold rowR2
  have h3 : ∀ (w2 : List (List (ℕ × SInt))) (y2 : List (List SInt)) (acc : List SInt),
      pairsR (fun w3 y3 acc3 => mulS cS (dotSpR y3 w3) :: acc3) w2 y2 acc =
        (w2.flatMap fun w3 => y2.flatMap fun y3 => [mulS cS (dotSpR y3 w3)]) ++ acc :=
    fun w2 y2 acc => pairsR_app (fun w3 y3 acc3 => mulS cS (dotSpR y3 w3) :: acc3)
      (fun w3 y3 => [mulS cS (dotSpR y3 w3)]) (fun _ _ _ => rfl) w2 y2 acc
  have h2 : ∀ (w1 : List (List (List (ℕ × SInt)))) (y1 : List (List (List SInt))) (acc : List SInt),
      pairsR (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotSpR y3 w3) :: acc3) w2 y2 acc2) w1 y1 acc =
        (w1.flatMap fun w2 => y1.flatMap fun y2 => w2.flatMap fun w3 => y2.flatMap fun y3 =>
          [mulS cS (dotSpR y3 w3)]) ++ acc :=
    fun w1 y1 acc => pairsR_app
      (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotSpR y3 w3) :: acc3) w2 y2 acc2)
      (fun w2 y2 => w2.flatMap fun w3 => y2.flatMap fun y3 => [mulS cS (dotSpR y3 w3)])
      (fun w2 y2 acc2 => h3 w2 y2 acc2) w1 y1 acc
  rw [pairsR_app
    (fun w1 y1 acc1 => pairsR (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotSpR y3 w3) :: acc3)
      w2 y2 acc2) w1 y1 acc1)
    (fun w1 y1 => w1.flatMap fun w2 => y1.flatMap fun y2 => w2.flatMap fun w3 => y2.flatMap fun y3 =>
      [mulS cS (dotSpR y3 w3)])
    (fun w1 y1 acc1 => h2 w1 y1 acc1), List.append_nil]

lemma itemRowsR2_eq (cS : SInt) (WrN : List (List (List (List (List (ℕ × SInt))))))
    (YN : List (List (List (List (List SInt))))) :
    itemRowsR2 cS WrN YN = WrN.flatMap fun wr0 => YN.map fun y0 => rowR2 cS wr0 y0 := by
  unfold itemRowsR2
  simp only [foldrR_eq]
  have hin : ∀ wr0 (a : List (List SInt)), YN.foldr (fun y0 acc' => rowR2 cS wr0 y0 :: acc') a =
      (YN.map fun y0 => rowR2 cS wr0 y0) ++ a := by
    intro wr0 a
    rw [IK.foldr_flatMap (fun y0 acc' => rowR2 cS wr0 y0 :: acc') (fun y0 => [rowR2 cS wr0 y0]) (fun _ _ => rfl) YN a,
      ← List.map_eq_flatMap]
  rw [IK.foldr_flatMap _ _ hin WrN [], List.append_nil]

lemma itemRowsC2_eq (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    itemRowsC2 C coef d0 d1 d2 d3 it =
      rowsF2 (C.types.getD it.1 default).W (C.Z.getD (C.types.getD it.1 default).zi default).zrows
        (C.Z.getD (C.types.getD it.1 default).zi default).n (it.2.1 * (d0 * d1 * d2 * d3))
        (it.2.2 * (d0 * d1 * d2 * d3)) (ofIntS coef) d0 d1 d2 d3 := by
  have hk : ∀ r : ℕ, Nat.mul r (Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3)) = r * (d0 * d1 * d2 * d3) := by
    intro r; simp only [Nat.mul_eq]; ring
  unfold itemRowsC2
  simp only []
  rw [padRows_eq, spPadRows_eq, spPadRows_eq, mapR_eq, List.map_map]
  simp only [dropR_eq, IK.getD_drop', hk]
  have hY : ((List.range (Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3))).map
      ((fun ws => mapR (fun zrow => dotSpR zrow ws)
        ((List.range (C.Z.getD (C.types.getD it.1 default).zi default).n).map fun v =>
          (List.range (C.Z.getD (C.types.getD it.1 default).zi default).n).map fun c =>
            ofIntS (((C.Z.getD (C.types.getD it.1 default).zi default).zrows.getD v []).getD c 0))) ∘
        fun v => spR ((List.range (C.Z.getD (C.types.getD it.1 default).zi default).n).map fun c =>
          ofIntS (((C.types.getD it.1 default).W.getD (it.2.2 * (d0 * d1 * d2 * d3) + v) []).getD c 0)))) =
      (List.range (Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3))).map fun v =>
        yRow2 (C.Z.getD (C.types.getD it.1 default).zi default).zrows (C.types.getD it.1 default).W
          (C.Z.getD (C.types.getD it.1 default).zi default).n (it.2.2 * (d0 * d1 * d2 * d3)) v := by
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply]
    rw [mapR_eq, List.map_map]
    rfl
  rw [hY, nest4R_range, nest4R_range, itemRowsR2_eq]
  unfold rowsF2
  simp only [List.flatMap_map, List.map_map]
  refine IK.flatMap_congr_mem fun μ0 _ => List.map_congr_left fun ν0 _ => ?_
  simp only [Function.comp_apply]
  rw [rowR2_eq]
  simp only [List.flatMap_map, ← List.map_eq_flatMap]
  simp only [List.map_map]
  rfl

/-! ### Values and shape -/

lemma entry_val (W Z : List (List Int)) (n kr ks : ℕ) (cS : SInt) (v v' : ℕ) :
    (mulS cS (dotSpR (yRow2 Z W n ks v') (spR (wRow W n kr v)))).val =
      (mulS cS (dotR (wRow W n kr v) (yRow Z W n ks v'))).val := by
  rw [mulS_eq, mulS_eq, SInt.val_mul, SInt.val_mul, dotSpR_spR]
  congr 1
  refine dotR_val_eq _ _ _ (by simp [yRow2, yRow]) fun i hi => ?_
  have hi' : i < n := by simpa [yRow2] using hi
  simp only [yRow2, yRow]
  rw [getD_range_map _ _ _ _ hi', getD_range_map _ _ _ _ hi', dotSpR_spR, dotR_val_comm]

lemma rowsF2_length (W Z : List (List Int)) (n kr ks : ℕ) (cS : SInt) (d0 d1 d2 d3 : ℕ) :
    (rowsF2 W Z n kr ks cS d0 d1 d2 d3).length = d0 * d0 := by
  unfold rowsF2
  exact len_flatMap_range d0 d0 _ (fun _ => by simp)

lemma rowsF2_rows (W Z : List (List Int)) (n kr ks : ℕ) (cS : SInt) (d0 d1 d2 d3 : ℕ) :
    ∀ r ∈ rowsF2 W Z n kr ks cS d0 d1 d2 d3, r.length = d1 * d1 * (d2 * d2 * (d3 * d3)) := by
  intro r hr
  unfold rowsF2 at hr
  simp only [List.mem_flatMap, List.mem_map] at hr
  obtain ⟨μ0, _, ν0, _, rfl⟩ := hr
  simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const', List.sum_replicate,
    smul_eq_mul]
  ring

end KI2

/-- **Shape of the item rows** (data-independent): `d0²` rows of `d1² d2² d3²` entries. -/
theorem itemRowsC2_shape (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    (itemRowsC2 C coef d0 d1 d2 d3 it).length = d0 * d0 ∧
      ∀ r ∈ itemRowsC2 C coef d0 d1 d2 d3 it, r.length = d1 * d1 * (d2 * d2 * (d3 * d3)) := by
  rw [KI2.itemRowsC2_eq]
  exact ⟨KI2.rowsF2_length _ _ _ _ _ _ _ _ _ _, KI2.rowsF2_rows _ _ _ _ _ _ _ _ _ _⟩

/-- **The sparse item rows have the values of the `KRItem` rows.** -/
theorem itemRowsC2_gv_C (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    ∀ k, gv (itemRowsC2 C coef d0 d1 d2 d3 it).flatten k = gv (itemRowsC C coef d0 d1 d2 d3 it).flatten k := by
  intro k
  rw [KI.gv_eq_vals, KI.gv_eq_vals]
  congr 1
  rw [KI2.itemRowsC2_eq, KI.itemRowsC_eq]
  unfold KI2.rowsF2 KI.rowsF
  rw [KI.flatten_flatMap_map, KI.flatten_flatMap_map]
  simp only [List.map_flatMap, List.map_map]
  refine IK.flatMap_congr_mem fun μ0 _ => IK.flatMap_congr_mem fun ν0 _ => IK.flatMap_congr_mem fun μ1 _ =>
    IK.flatMap_congr_mem fun ν1 _ => IK.flatMap_congr_mem fun μ2 _ => IK.flatMap_congr_mem fun ν2 _ =>
    IK.flatMap_congr_mem fun μ3 _ => List.map_congr_left fun ν3 _ => ?_
  simp only [Function.comp_apply]
  exact KI2.entry_val _ _ _ _ _ _ _ _

/-- **The sparse item rows have the values of `itemTF`** (block without corrections, `zmul = 1`). -/
theorem itemRowsC2_gv (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ)
    (hu : (C.Z.getD (C.types.getD it.1 default).zi default).uent = []) :
    ∀ k, gv (itemRowsC2 C coef d0 d1 d2 d3 it).flatten k = gv (itemTF C 1 coef d0 d1 d2 d3 it) k := fun k => by
  rw [itemRowsC2_gv_C, itemRowsC_gv C coef d0 d1 d2 d3 it hu]

namespace KI2

lemma leafRowsC2_rows (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) : ∀ (items : List (ℕ × ℕ × ℕ)),
    ∀ r ∈ leafRowsC2 C coef d0 d1 d2 d3 items, r.length = d1 * d1 * (d2 * d2 * (d3 * d3))
  | [] => by
    intro r hr
    change r ∈ ([] : List (List SInt)) at hr
    simp at hr
  | it :: items => by
    show ∀ r ∈ addRowsR (itemRowsC2 C coef d0 d1 d2 d3 it) (leafRowsC2 C coef d0 d1 d2 d3 items), _
    exact KI.addRowsR_rows _ _ _ (itemRowsC2_shape C coef d0 d1 d2 d3 it).2
      (leafRowsC2_rows C coef d0 d1 d2 d3 items)

lemma leafRowsC2_length (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) : ∀ (items : List (ℕ × ℕ × ℕ)),
    (leafRowsC2 C coef d0 d1 d2 d3 items).length = if items = [] then 0 else d0 * d0
  | [] => by
    show ([] : List (List SInt)).length = if ([] : List (ℕ × ℕ × ℕ)) = [] then 0 else d0 * d0
    simp
  | it :: items => by
    show (addRowsR (itemRowsC2 C coef d0 d1 d2 d3 it) (leafRowsC2 C coef d0 d1 d2 d3 items)).length = _
    rw [KI.addRowsR_length, (itemRowsC2_shape C coef d0 d1 d2 d3 it).1, leafRowsC2_length C coef d0 d1 d2 d3 items]
    split_ifs <;> simp_all

end KI2

/-- **Shape of the leaf rows**: `d0²` rows of `d1² d2² d3²` entries (for a nonempty leaf). -/
theorem leafRowsC2_shape (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ))
    (hne : items ≠ []) :
    (leafRowsC2 C coef d0 d1 d2 d3 items).length = d0 * d0 ∧
      ∀ r ∈ leafRowsC2 C coef d0 d1 d2 d3 items, r.length = d1 * d1 * (d2 * d2 * (d3 * d3)) := by
  refine ⟨?_, KI2.leafRowsC2_rows C coef d0 d1 d2 d3 items⟩
  rw [KI2.leafRowsC2_length, ite_eq_right hne]

/-- **The leaf rows have the values of the summed `itemTF` tensors** (blocks without corrections, `zmul = 1`). -/
theorem leafRowsC2_gv (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ))
    (hu : ∀ it ∈ items, (C.Z.getD (C.types.getD it.1 default).zi default).uent = []) :
    ∀ k, gv (leafRowsC2 C coef d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF C 1 coef d0 d1 d2 d3)).foldr addL []) k := by
  induction items with
  | nil => intro k; rfl
  | cons it items ih =>
    intro k
    show gv (addRowsR (itemRowsC2 C coef d0 d1 d2 d3 it) (leafRowsC2 C coef d0 d1 d2 d3 items)).flatten k = _
    rw [KI.flatten_addRowsR_gv _ _ _ (itemRowsC2_shape C coef d0 d1 d2 d3 it).2
      (KI2.leafRowsC2_rows C coef d0 d1 d2 d3 items), itemRowsC2_gv C coef d0 d1 d2 d3 it (hu it (by simp)),
      ih (fun it' h => hu it' (by simp [h])), List.map_cons, List.foldr_cons, gv_addL]

/-- The sparse leaf rows have the shape `hsum_of_checks` needs. -/
theorem leafRowsC2_LRShape (C : CertD) (coef : Int) : LRShape (leafRowsC2 C coef) := by
  intro d0 d1 d2 d3 items
  by_cases hne : items = []
  · subst hne
    exact ⟨Or.inr rfl, fun r hr => by simp [leafRowsC2, foldrR] at hr⟩
  · obtain ⟨hl, hr⟩ := leafRowsC2_shape C coef d0 d1 d2 d3 items hne
    refine ⟨Or.inl hl, fun r hmem => ?_⟩
    rw [hr r hmem]; ring

/-- On the reduced certificate, the sparse leaf rows have the `itemTF` values. -/
theorem leafRowsC2_hleaf (p zmul : ℕ) (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ)) (k : ℕ) :
    gv (leafRowsC2 (certModR p zmul C) coef d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 coef d0 d1 d2 d3)).foldr addL []) k := by
  rw [certModR_eq]
  exact leafRowsC2_gv _ coef d0 d1 d2 d3 items (fun it _ => certMod_uent p zmul C _) k

end NPT.Cert.KR
