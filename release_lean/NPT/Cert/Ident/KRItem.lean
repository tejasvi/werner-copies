/-
NPT.Cert.Ident.KRItem — recursor-encoded item rows.
`itemRowsC` computes the `d0²` leaf rows of a rule-group item with raw recursors only (`KRLib`), from a block whose
corrections are folded in (`uent = []`, used with `zmul = 1`, as in the mod-`p` certificate). Its shape does not
depend on the data (`itemRowsC_shape`), and its flattened entries have the values of `itemTF` (`itemRowsC_gv`).
`leafRowsC` sums the rows over the items of a leaf (`leafRowsC_shape`, `leafRowsC_gv`).
-/
import NPT.Cert.Ident.KRRed
import NPT.Cert.Ident.ItemK

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident

namespace NPT.Cert.KR

/-- The leaf rows of one item `(t, r, s)`: row `i0 = μ0·d0 + ν0`, entries `(i1, i2, i3)` in order (recursors only). -/
noncomputable def itemRowsC (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) : List (List SInt) :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let nn := Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3)
  let Zq := mapR (fun row => mapR ofIntS (takePadR b.n 0 row)) (takePadR b.n [] b.zrows)
  let Wr := mapR (fun row => mapR ofIntS (takePadR b.n 0 row)) (takePadR nn [] (dropR (Nat.mul it.2.1 nn) t.W))
  let Ws := mapR (fun row => mapR ofIntS (takePadR b.n 0 row)) (takePadR nn [] (dropR (Nat.mul it.2.2 nn) t.W))
  let Y := mapR (fun ws => mapR (fun zrow => dotR zrow ws) Zq) Ws
  itemRowsR (ofIntS coef) (nest4R d0 d1 d2 d3 Wr) (nest4R d0 d1 d2 d3 Y)

/-- The leaf rows of a leaf: the row-wise sum of its items' rows. -/
noncomputable def leafRowsC (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ)) :
    List (List SInt) :=
  foldrR (fun it acc => addRowsR (itemRowsC C coef d0 d1 d2 d3 it) acc) [] items

namespace KI

/-! ### Lists -/

lemma len_flatMap_range {β : Type} (n m : ℕ) (g : ℕ → List β) (hg : ∀ i, (g i).length = m) :
    ((List.range n).flatMap g).length = n * m := by
  rw [List.length_flatMap]
  simp only [hg, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-- Groups of a range map. -/
lemma grpR_range {α : Type} (m : ℕ) : ∀ (k : ℕ) (f : ℕ → α),
    grpR m k ((List.range (k * m)).map f) = (List.range k).map fun i => (List.range m).map fun j => f (i * m + j)
  | 0, f => rfl
  | k + 1, f => by
    have hsplit : (List.range ((k + 1) * m)).map f =
        (List.range m).map f ++ (List.range (k * m)).map fun i => f (m + i) := by
      rw [show (k + 1) * m = m + k * m by ring, List.range_add, List.map_append, List.map_map]
      rfl
    show takeR m ((List.range ((k + 1) * m)).map f) :: grpR m k (dropR m ((List.range ((k + 1) * m)).map f)) = _
    rw [takeR_eq, dropR_eq, hsplit, List.take_left' (by simp), List.drop_left' (by simp), grpR_range m k,
      List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · simp
    · refine List.map_congr_left fun i _ => List.map_congr_left fun j _ => ?_
      congr 1
      simp only [Nat.succ_eq_add_one]
      ring

/-- The digit nest of a range map. -/
lemma nest4R_range {α : Type} (d0 d1 d2 d3 : ℕ) (f : ℕ → α) :
    nest4R d0 d1 d2 d3 ((List.range (Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3))).map f) =
      (List.range d0).map fun a => (List.range d1).map fun b => (List.range d2).map fun c =>
        (List.range d3).map fun e => f (mr4 d0 d1 d2 d3 a b c e) := by
  unfold nest4R
  simp only [Nat.mul_eq]
  rw [show d0 * d1 * (d2 * d3) = d0 * (d1 * (d2 * d3)) by ring, grpR_range, mapR_eq, List.map_map]
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp_apply]
  rw [grpR_range, mapR_eq, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply]
  rw [grpR_range]
  refine List.map_congr_left fun c _ => List.map_congr_left fun e _ => ?_
  congr 1
  unfold mr4
  ring

lemma pairsR_app {β γ δ : Type} (f : β → γ → List δ → List δ) (g : β → γ → List δ)
    (hf : ∀ x y acc, f x y acc = g x y ++ acc) (xs : List β) (ys : List γ) (acc : List δ) :
    pairsR f xs ys acc = (xs.flatMap fun x => ys.flatMap fun y => g x y) ++ acc := by
  unfold pairsR
  simp only [foldrR_eq]
  exact IK.foldr_flatMap _ _ (fun x a => IK.foldr_flatMap _ _ (fun y a' => hf x y a') ys a) xs acc

lemma rowR_eq (cS : SInt) (wr0 y0 : List (List (List (List SInt)))) :
    rowR cS wr0 y0 = wr0.flatMap fun w1 => y0.flatMap fun y1 => w1.flatMap fun w2 => y1.flatMap fun y2 =>
      w2.flatMap fun w3 => y2.flatMap fun y3 => [mulS cS (dotR w3 y3)] := by
  unfold rowR
  have h3 : ∀ (w2 y2 : List (List SInt)) (acc : List SInt),
      pairsR (fun w3 y3 acc3 => mulS cS (dotR w3 y3) :: acc3) w2 y2 acc =
        (w2.flatMap fun w3 => y2.flatMap fun y3 => [mulS cS (dotR w3 y3)]) ++ acc :=
    fun w2 y2 acc => pairsR_app (fun w3 y3 acc3 => mulS cS (dotR w3 y3) :: acc3)
      (fun w3 y3 => [mulS cS (dotR w3 y3)]) (fun _ _ _ => rfl) w2 y2 acc
  have h2 : ∀ (w1 y1 : List (List (List SInt))) (acc : List SInt),
      pairsR (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotR w3 y3) :: acc3) w2 y2 acc2) w1 y1 acc =
        (w1.flatMap fun w2 => y1.flatMap fun y2 => w2.flatMap fun w3 => y2.flatMap fun y3 =>
          [mulS cS (dotR w3 y3)]) ++ acc :=
    fun w1 y1 acc => pairsR_app
      (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotR w3 y3) :: acc3) w2 y2 acc2)
      (fun w2 y2 => w2.flatMap fun w3 => y2.flatMap fun y3 => [mulS cS (dotR w3 y3)])
      (fun w2 y2 acc2 => h3 w2 y2 acc2) w1 y1 acc
  rw [pairsR_app
    (fun w1 y1 acc1 => pairsR (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotR w3 y3) :: acc3)
      w2 y2 acc2) w1 y1 acc1)
    (fun w1 y1 => w1.flatMap fun w2 => y1.flatMap fun y2 => w2.flatMap fun w3 => y2.flatMap fun y3 =>
      [mulS cS (dotR w3 y3)])
    (fun w1 y1 acc1 => h2 w1 y1 acc1), List.append_nil]

lemma itemRowsR_eq (cS : SInt) (WrN YN : List (List (List (List (List SInt))))) :
    itemRowsR cS WrN YN = WrN.flatMap fun wr0 => YN.map fun y0 => rowR cS wr0 y0 := by
  unfold itemRowsR
  simp only [foldrR_eq]
  have hin : ∀ wr0 (a : List (List SInt)), YN.foldr (fun y0 acc' => rowR cS wr0 y0 :: acc') a =
      (YN.map fun y0 => rowR cS wr0 y0) ++ a := by
    intro wr0 a
    rw [IK.foldr_flatMap (fun y0 acc' => rowR cS wr0 y0 :: acc') (fun y0 => [rowR cS wr0 y0]) (fun _ _ => rfl) YN a,
      ← List.map_eq_flatMap]
  rw [IK.foldr_flatMap _ _ hin WrN [], List.append_nil]

lemma flatten_flatMap_map {α β γ : Type} (l1 : List α) (l2 : List β) (R : α → β → List γ) :
    (l1.flatMap fun x => l2.map fun y => R x y).flatten = l1.flatMap fun x => l2.flatMap fun y => R x y := by
  induction l1 with
  | nil => rfl
  | cons x l1 ih => rw [List.flatMap_cons, List.flatten_append, ih, List.flatMap_cons]; rfl

/-! ### Index form of the item rows -/

/-- Row `v` of `W` from offset `k`, padded to `n` entries. -/
noncomputable def wRow (W : List (List Int)) (n k v : ℕ) : List SInt :=
  (List.range n).map fun a => ofIntS ((W.getD (k + v) []).getD a 0)

/-- Row `a` of `Z`, padded to `n` entries. -/
noncomputable def zRow (Z : List (List Int)) (n a : ℕ) : List SInt :=
  (List.range n).map fun c => ofIntS ((Z.getD a []).getD c 0)

/-- Row `v` of `Y = Z · Sᵀ` (`S` = rows of `W` from offset `k`). -/
noncomputable def yRow (Z W : List (List Int)) (n k v : ℕ) : List SInt :=
  (List.range n).map fun a => dotR (zRow Z n a) (wRow W n k v)

/-- The leaf rows in index form: row `(μ0, ν0)`, entries `(μ1 ν1 μ2 ν2 μ3 ν3)` in order. -/
noncomputable def rowsF (W Z : List (List Int)) (n kr ks : ℕ) (cS : SInt) (d0 d1 d2 d3 : ℕ) : List (List SInt) :=
  (List.range d0).flatMap fun μ0 => (List.range d0).map fun ν0 =>
    (List.range d1).flatMap fun μ1 => (List.range d1).flatMap fun ν1 =>
    (List.range d2).flatMap fun μ2 => (List.range d2).flatMap fun ν2 =>
    (List.range d3).flatMap fun μ3 => (List.range d3).map fun ν3 =>
      mulS cS (dotR (wRow W n kr (mr4 d0 d1 d2 d3 μ0 μ1 μ2 μ3)) (yRow Z W n ks (mr4 d0 d1 d2 d3 ν0 ν1 ν2 ν3)))

lemma padRows_eq (n m : ℕ) (L : List (List Int)) :
    mapR (fun row => mapR ofIntS (takePadR m 0 row)) (takePadR n [] L) =
      (List.range n).map fun v => (List.range m).map fun c => ofIntS ((L.getD v []).getD c 0) := by
  rw [takePadR_eq, mapR_eq, List.map_map]
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply]
  rw [mapR_eq, takePadR_eq, List.map_map]
  rfl

lemma itemRowsC_eq (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    itemRowsC C coef d0 d1 d2 d3 it =
      rowsF (C.types.getD it.1 default).W (C.Z.getD (C.types.getD it.1 default).zi default).zrows
        (C.Z.getD (C.types.getD it.1 default).zi default).n (it.2.1 * (d0 * d1 * d2 * d3))
        (it.2.2 * (d0 * d1 * d2 * d3)) (ofIntS coef) d0 d1 d2 d3 := by
  have hk : ∀ r : ℕ, Nat.mul r (Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3)) = r * (d0 * d1 * d2 * d3) := by
    intro r; simp only [Nat.mul_eq]; ring
  unfold itemRowsC
  simp only []
  rw [padRows_eq, padRows_eq, padRows_eq, mapR_eq, List.map_map]
  simp only [dropR_eq, IK.getD_drop', hk]
  have hY : ((List.range (Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3))).map
      ((fun ws => mapR (fun zrow => dotR zrow ws)
        ((List.range (C.Z.getD (C.types.getD it.1 default).zi default).n).map fun v =>
          (List.range (C.Z.getD (C.types.getD it.1 default).zi default).n).map fun c =>
            ofIntS (((C.Z.getD (C.types.getD it.1 default).zi default).zrows.getD v []).getD c 0))) ∘
        fun v => (List.range (C.Z.getD (C.types.getD it.1 default).zi default).n).map fun c =>
          ofIntS (((C.types.getD it.1 default).W.getD (it.2.2 * (d0 * d1 * d2 * d3) + v) []).getD c 0))) =
      (List.range (Nat.mul (Nat.mul d0 d1) (Nat.mul d2 d3))).map fun v =>
        yRow (C.Z.getD (C.types.getD it.1 default).zi default).zrows (C.types.getD it.1 default).W
          (C.Z.getD (C.types.getD it.1 default).zi default).n (it.2.2 * (d0 * d1 * d2 * d3)) v := by
    refine List.map_congr_left fun v _ => ?_
    simp only [Function.comp_apply]
    rw [mapR_eq, List.map_map]
    rfl
  rw [hY, nest4R_range, nest4R_range, itemRowsR_eq]
  unfold rowsF
  simp only [List.flatMap_map, List.map_map]
  refine IK.flatMap_congr_mem fun μ0 _ => List.map_congr_left fun ν0 _ => ?_
  simp only [Function.comp_apply]
  rw [rowR_eq]
  simp only [List.flatMap_map, ← List.map_eq_flatMap]
  simp only [List.map_map]
  rfl

/-! ### Shape of the index form -/

lemma rowsF_length (W Z : List (List Int)) (n kr ks : ℕ) (cS : SInt) (d0 d1 d2 d3 : ℕ) :
    (rowsF W Z n kr ks cS d0 d1 d2 d3).length = d0 * d0 := by
  unfold rowsF
  exact len_flatMap_range d0 d0 _ (fun _ => by simp)

lemma rowsF_rows (W Z : List (List Int)) (n kr ks : ℕ) (cS : SInt) (d0 d1 d2 d3 : ℕ) :
    ∀ r ∈ rowsF W Z n kr ks cS d0 d1 d2 d3, r.length = d1 * d1 * (d2 * d2 * (d3 * d3)) := by
  intro r hr
  unfold rowsF at hr
  simp only [List.mem_flatMap, List.mem_map] at hr
  obtain ⟨μ0, _, ν0, _, rfl⟩ := hr
  simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const', List.sum_replicate,
    smul_eq_mul]
  ring

/-! ### Values -/

lemma gv_eq_vals : ∀ (L : List SInt) (k : ℕ), gv L k = (L.map SInt.val).getD k 0
  | [], k => by simp
  | x :: L, 0 => by simp
  | x :: L, k + 1 => by simp [gv_eq_vals L k]

/-- One entry of the index form has the value of the `itemTF` entry (`zmul = 1`, no corrections). -/
lemma leaf_val (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ)
    (hu : (C.Z.getD (C.types.getD it.1 default).zi default).uent = [])
    {μ0 ν0 μ1 ν1 μ2 ν2 μ3 ν3 : ℕ} (hν0 : ν0 < d0) (hν1 : ν1 < d1) (hν2 : ν2 < d2) (hν3 : ν3 < d3) :
    (mulS (ofIntS coef) (dotR
      (wRow (C.types.getD it.1 default).W (C.Z.getD (C.types.getD it.1 default).zi default).n
        (it.2.1 * (d0 * d1 * d2 * d3)) (mr4 d0 d1 d2 d3 μ0 μ1 μ2 μ3))
      (yRow (C.Z.getD (C.types.getD it.1 default).zi default).zrows (C.types.getD it.1 default).W
        (C.Z.getD (C.types.getD it.1 default).zi default).n (it.2.2 * (d0 * d1 * d2 * d3))
        (mr4 d0 d1 d2 d3 ν0 ν1 ν2 ν3)))).val =
      itemE C 1 coef d0 d1 d2 d3 it (itemY C 1 d0 d1 d2 d3 it) (μ0 * d0 + ν0) (μ1 * d1 + ν1) (μ2 * d2 + ν2)
        (μ3 * d3 + ν3) := by
  obtain ⟨q0, r0⟩ := IK.divmod_eq (a := μ0) hν0
  obtain ⟨q1, r1⟩ := IK.divmod_eq (a := μ1) hν1
  obtain ⟨q2, r2⟩ := IK.divmod_eq (a := μ2) hν2
  obtain ⟨q3, r3⟩ := IK.divmod_eq (a := μ3) hν3
  have hv : mr4 d0 d1 d2 d3 ν0 ν1 ν2 ν3 < d0 * d1 * d2 * d3 := mr4_lt _ _ _ _ _ _ _ _ hν0 hν1 hν2 hν3
  rw [mulS_eq, SInt.val_mul, ofIntS_eq, SInt.val_ofInt, dotR_eq, dotS_val]
  unfold itemE
  simp only [q0, r0, q1, r1, q2, r2, q3, r3, wRow, yRow, List.length_map, List.length_range, min_self]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.1 ha
  rw [getD_range_map _ _ _ _ ha', getD_range_map _ _ _ _ ha', itemY_entry C 1 d0 d1 d2 d3 it _ a hv ha',
    dotR_eq, dotS_val]
  simp only [ofIntS_eq, SInt.val_ofInt]
  congr 1
  simp only [zRow, List.length_map, List.length_range, min_self]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' := Finset.mem_range.1 hc
  rw [getD_range_map _ _ _ _ hc', getD_range_map _ _ _ _ hc']
  simp only [ofIntS_eq, SInt.val_ofInt]
  congr 1
  unfold zqI NPT.Cert.PBlock.ufind NPT.Cert.PBlock.zget
  rw [hu]
  simp

/-- `itemTF` with each leaf index split into its two digits. -/
lemma itemTF_eq (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    itemTF C zmul coef d0 d1 d2 d3 it =
      (List.range d0).flatMap fun μ0 => (List.range d0).flatMap fun ν0 =>
      (List.range d1).flatMap fun μ1 => (List.range d1).flatMap fun ν1 =>
      (List.range d2).flatMap fun μ2 => (List.range d2).flatMap fun ν2 =>
      (List.range d3).flatMap fun μ3 => (List.range d3).map fun ν3 =>
        SInt.ofInt (itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it)
          (μ0 * d0 + ν0) (μ1 * d1 + ν1) (μ2 * d2 + ν2) (μ3 * d3 + ν3)) := by
  unfold itemTF
  simp only [IK.flatMap_range_sq, IK.map_range_sq]

/-! ### Row sums -/

lemma addL_length : ∀ (xs ys : List SInt), (addL xs ys).length = max xs.length ys.length
  | [], ys => by simp [addL]
  | x :: xs, [] => by simp [addL]
  | x :: xs, y :: ys => by simp only [addL, List.length_cons, addL_length xs ys]; omega

lemma gv_append (X Y : List SInt) (k : ℕ) :
    gv (X ++ Y) k = if k < X.length then gv X k else gv Y (k - X.length) := by
  unfold gv
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_not_lt h), ← List.getD_eq_getElem?_getD]

lemma addRowsR_length : ∀ (A B : List (List SInt)), (addRowsR A B).length = max A.length B.length
  | [], B => by show B.length = max 0 B.length; simp
  | a :: A, [] => by show (a :: A).length = max (a :: A).length 0; simp
  | a :: A, b :: B => by
    show (addLR a b :: addRowsR A B).length = max (a :: A).length (b :: B).length
    simp only [List.length_cons, addRowsR_length A B]
    omega

lemma addRowsR_rows (M : ℕ) : ∀ (A B : List (List SInt)), (∀ r ∈ A, r.length = M) → (∀ r ∈ B, r.length = M) →
    ∀ r ∈ addRowsR A B, r.length = M
  | [], B, _, hB => fun r hr => hB r hr
  | a :: A, [], hA, _ => fun r hr => hA r hr
  | a :: A, b :: B, hA, hB => by
    intro r hr
    change r ∈ addLR a b :: addRowsR A B at hr
    rcases List.mem_cons.1 hr with rfl | hr
    · rw [addLR_eq, addL_length, hA a (by simp), hB b (by simp), max_self]
    · exact addRowsR_rows M A B (fun r h => hA r (by simp [h])) (fun r h => hB r (by simp [h])) r hr

/-- Row sums of rows of one length add the flattened values. -/
lemma flatten_addRowsR_gv (M : ℕ) : ∀ (A B : List (List SInt)), (∀ r ∈ A, r.length = M) →
    (∀ r ∈ B, r.length = M) → ∀ k, gv (addRowsR A B).flatten k = gv A.flatten k + gv B.flatten k
  | [], B, _, _, k => by
    show gv B.flatten k = gv ([] : List (List SInt)).flatten k + gv B.flatten k
    simp
  | a :: A, [], _, _, k => by
    show gv (a :: A).flatten k = gv (a :: A).flatten k + gv ([] : List (List SInt)).flatten k
    simp
  | a :: A, b :: B, hA, hB, k => by
    show gv (addLR a b :: addRowsR A B).flatten k = gv (a :: A).flatten k + gv (b :: B).flatten k
    have ha := hA a (by simp)
    have hb := hB b (by simp)
    have hab : (addLR a b).length = M := by rw [addLR_eq, addL_length, ha, hb, max_self]
    simp only [List.flatten_cons]
    rw [gv_append, gv_append, gv_append, hab, ha, hb]
    split_ifs with h
    · rw [addLR_eq, gv_addL]
    · exact flatten_addRowsR_gv M A B (fun r hr => hA r (by simp [hr])) (fun r hr => hB r (by simp [hr])) (k - M)

end KI

/-- **Shape of the item rows** (data-independent): `d0²` rows of `d1² d2² d3²` entries. -/
theorem itemRowsC_shape (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    (itemRowsC C coef d0 d1 d2 d3 it).length = d0 * d0 ∧
      ∀ r ∈ itemRowsC C coef d0 d1 d2 d3 it, r.length = d1 * d1 * (d2 * d2 * (d3 * d3)) := by
  rw [KI.itemRowsC_eq]
  exact ⟨KI.rowsF_length _ _ _ _ _ _ _ _ _ _, KI.rowsF_rows _ _ _ _ _ _ _ _ _ _⟩

/-- **The item rows have the values of `itemTF`** (block without corrections, `zmul = 1`). -/
theorem itemRowsC_gv (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ)
    (hu : (C.Z.getD (C.types.getD it.1 default).zi default).uent = []) :
    ∀ k, gv (itemRowsC C coef d0 d1 d2 d3 it).flatten k = gv (itemTF C 1 coef d0 d1 d2 d3 it) k := by
  intro k
  rw [KI.gv_eq_vals, KI.gv_eq_vals]
  congr 1
  rw [KI.itemRowsC_eq, KI.itemTF_eq]
  unfold KI.rowsF
  rw [KI.flatten_flatMap_map]
  simp only [List.map_flatMap, List.map_map]
  refine IK.flatMap_congr_mem fun μ0 _ => IK.flatMap_congr_mem fun ν0 hν0 => IK.flatMap_congr_mem fun μ1 _ =>
    IK.flatMap_congr_mem fun ν1 hν1 => IK.flatMap_congr_mem fun μ2 _ => IK.flatMap_congr_mem fun ν2 hν2 =>
    IK.flatMap_congr_mem fun μ3 _ => List.map_congr_left fun ν3 hν3 => ?_
  simp only [List.mem_range] at hν0 hν1 hν2 hν3
  simp only [Function.comp_apply]
  rw [SInt.val_ofInt]
  exact KI.leaf_val C coef d0 d1 d2 d3 it hu hν0 hν1 hν2 hν3

namespace KI

lemma leafRowsC_rows (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) : ∀ (items : List (ℕ × ℕ × ℕ)),
    ∀ r ∈ leafRowsC C coef d0 d1 d2 d3 items, r.length = d1 * d1 * (d2 * d2 * (d3 * d3))
  | [] => by
    intro r hr
    change r ∈ ([] : List (List SInt)) at hr
    simp at hr
  | it :: items => by
    show ∀ r ∈ addRowsR (itemRowsC C coef d0 d1 d2 d3 it) (leafRowsC C coef d0 d1 d2 d3 items), _
    exact addRowsR_rows _ _ _ (itemRowsC_shape C coef d0 d1 d2 d3 it).2 (leafRowsC_rows C coef d0 d1 d2 d3 items)

lemma leafRowsC_length (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) : ∀ (items : List (ℕ × ℕ × ℕ)),
    (leafRowsC C coef d0 d1 d2 d3 items).length = if items = [] then 0 else d0 * d0
  | [] => by
    show ([] : List (List SInt)).length = if ([] : List (ℕ × ℕ × ℕ)) = [] then 0 else d0 * d0
    simp
  | it :: items => by
    show (addRowsR (itemRowsC C coef d0 d1 d2 d3 it) (leafRowsC C coef d0 d1 d2 d3 items)).length = _
    rw [addRowsR_length, (itemRowsC_shape C coef d0 d1 d2 d3 it).1, leafRowsC_length C coef d0 d1 d2 d3 items]
    split_ifs <;> simp_all

end KI

/-- **Shape of the leaf rows**: `d0²` rows of `d1² d2² d3²` entries (for a nonempty leaf). -/
theorem leafRowsC_shape (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ)) (hne : items ≠ []) :
    (leafRowsC C coef d0 d1 d2 d3 items).length = d0 * d0 ∧
      ∀ r ∈ leafRowsC C coef d0 d1 d2 d3 items, r.length = d1 * d1 * (d2 * d2 * (d3 * d3)) := by
  refine ⟨?_, KI.leafRowsC_rows C coef d0 d1 d2 d3 items⟩
  rw [KI.leafRowsC_length, ite_eq_right hne]

/-- **The leaf rows have the values of the summed `itemTF` tensors** (blocks without corrections, `zmul = 1`). -/
theorem leafRowsC_gv (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ))
    (hu : ∀ it ∈ items, (C.Z.getD (C.types.getD it.1 default).zi default).uent = []) :
    ∀ k, gv (leafRowsC C coef d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF C 1 coef d0 d1 d2 d3)).foldr addL []) k := by
  induction items with
  | nil => intro k; rfl
  | cons it items ih =>
    intro k
    show gv (addRowsR (itemRowsC C coef d0 d1 d2 d3 it) (leafRowsC C coef d0 d1 d2 d3 items)).flatten k = _
    rw [KI.flatten_addRowsR_gv _ _ _ (itemRowsC_shape C coef d0 d1 d2 d3 it).2
      (KI.leafRowsC_rows C coef d0 d1 d2 d3 items), itemRowsC_gv C coef d0 d1 d2 d3 it (hu it (by simp)),
      ih (fun it' h => hu it' (by simp [h])), List.map_cons, List.foldr_cons, gv_addL]

end NPT.Cert.KR
