/-
NPT.Cert.Ident.KRSplit — one family's mod-`p` check split over several kernel declarations.
Declaration `j` packs the parts of a subset of the rule groups (plus any other parts), routes its fields from the class
tree with leaf `i` starting at the offset `offs_j[i]`, and checks every class mod `p` (`checkKRo`).  If the offsets of
all declarations sum to `0 mod p` leafwise, the class sums of the whole family vanish mod `p`
(`classSums_modP_split`), so each declaration only holds its own groups' slices.
-/
import NPT.Cert.Ident.KRIdFactB

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident NPT.Brauer

namespace NPT.Cert.KR

/-! ### Routing from a class tree with offsets -/

lemma getD_app_left {α : Type} (A B : List α) (j : ℕ) (d : α) (h : j < A.length) : (A ++ B).getD j d = A.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

lemma getD_app_right {α : Type} (A B : List α) (j : ℕ) (d : α) (h : A.length ≤ j) :
    (A ++ B).getD j d = B.getD (j - A.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

/-- The routing tree of the class tree `t0` whose `i`-th leaf (in order) starts at sum `offs[i]`; second component:
the unused offsets. -/
def toRTo : AT → List ℕ → RT × List ℕ
  | .leaf k _ _, offs => (.leaf k (offs.headD 0) 0 true, offs.tail)
  | .node k l r, offs =>
    let a := toRTo l offs
    let b := toRTo r a.2
    (.node k a.1 b.1, b.2)

theorem toRTo_snd : ∀ (t : AT) (offs : List ℕ), (toRTo t offs).2 = offs.drop t.leaves.length
  | .leaf _ _ _, offs => by simp [toRTo, AT.leaves]
  | .node k l r, offs => by
    simp only [toRTo, AT.leaves, List.length_append]
    rw [toRTo_snd r, toRTo_snd l, List.drop_drop]

theorem toRTo_length : ∀ (t : AT) (offs : List ℕ), (toRTo t offs).1.leaves.length = t.leaves.length
  | .leaf _ _ _, offs => by simp [toRTo, AT.leaves, RT.leaves]
  | .node k l r, offs => by
    simp only [toRTo, AT.leaves, RT.leaves, List.length_append]
    rw [toRTo_length l, toRTo_length r]

theorem toRTo_getD : ∀ (t : AT) (offs : List ℕ) (j : ℕ), j < t.leaves.length →
    (toRTo t offs).1.leaves.getD j dLeafR = ((t.leaves.getD j dLeaf).1, offs.getD j 0, 0, true)
  | .leaf k s ok, offs, j, hj => by
    simp only [AT.leaves, List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    cases offs <;> simp [toRTo, RT.leaves, AT.leaves]
  | .node k l r, offs, j, hj => by
    simp only [toRTo, AT.leaves, RT.leaves]
    simp only [AT.leaves, List.length_append] at hj
    by_cases hjl : j < l.leaves.length
    · have h1 : j < (toRTo l offs).1.leaves.length := by rw [toRTo_length]; exact hjl
      rw [getD_app_left _ _ _ _ h1, getD_app_left _ _ _ _ hjl, toRTo_getD l offs j hjl]
    · have hjl' : l.leaves.length ≤ j := Nat.le_of_not_lt hjl
      have h1 : (toRTo l offs).1.leaves.length ≤ j := by rw [toRTo_length]; exact hjl'
      rw [getD_app_right _ _ _ _ h1, getD_app_right _ _ _ _ hjl', toRTo_length,
        toRTo_getD r _ (j - l.leaves.length) (by omega), toRTo_snd, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' hjl', List.getD_eq_getElem?_getD]

theorem toRTo_tgt : ∀ (t : AT) (offs : List ℕ) (key : ℕ), (toRTo t offs).1.tgt key = t.tgt key
  | .leaf _ _ _, _, _ => by simp [toRTo, RT.tgt, AT.tgt]
  | .node k l r, offs, key => by
    simp only [toRTo, RT.tgt, AT.tgt, toRTo_tgt l, toRTo_tgt r, toRTo_length]

/-- **Soundness of the offset check.** If `RT.okMod p h` holds after routing the values `vs` with keys `cs` from
`toRTo t0 offs`, then for every position `q`, the offset of `q`'s leaf plus the values with the key of `q` is their
number times `h`, modulo `p`. -/
theorem okMod_sound_off (p h : ℕ) (vs cs : List ℕ) (t0 : AT) (offs : List ℕ)
    (hok : RT.okMod p h (routeR vs cs (toRTo t0 offs).1) = true)
    (hlen : vs.length = cs.length) (q : ℕ) (hq : q < vs.length) :
    (offs.getD (t0.tgt (cs.getD q 0)) 0 +
      ∑ q' ∈ range vs.length, (if cs.getD q' 0 = cs.getD q 0 then vs.getD q' 0 else 0)) % p =
      (((range vs.length).filter fun q' => cs.getD q' 0 = cs.getD q 0).card * h) % p := by
  obtain ⟨hL, _, hJ⟩ := routeR_spec vs cs (toRTo t0 offs).1 hlen
  set j := t0.tgt (cs.getD q 0) with hj
  have hjl : j < t0.leaves.length := AT.tgt_lt t0 _
  have hjl' : j < (toRTo t0 offs).1.leaves.length := by rw [toRTo_length]; exact hjl
  obtain ⟨h1, h2, h3, h4, _⟩ := hJ j hjl'
  simp only [toRTo_tgt, toRTo_getD t0 offs j hjl] at h1 h2 h3 h4
  have hmem : (routeR vs cs (toRTo t0 offs).1).leaves.getD j dLeafR ∈ (routeR vs cs (toRTo t0 offs).1).leaves := by
    have hlt : j < (routeR vs cs (toRTo t0 offs).1).leaves.length := by rw [hL]; exact hjl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
  obtain ⟨hflag, hmod⟩ := (RT.okMod_iff p h _).1 hok _ hmem
  have hkey := h4 hflag
  have hcq : cs.getD q 0 = (t0.leaves.getD j dLeaf).1 := hkey q hq rfl
  have hiff : ∀ q' < vs.length, (t0.tgt (cs.getD q' 0) = j ↔ cs.getD q' 0 = cs.getD q 0) := by
    intro q' hq'
    constructor
    · intro ht; rw [hkey q' hq' ht, hcq]
    · intro he; rw [he]
  have hsum : (∑ q' ∈ range vs.length, (if cs.getD q' 0 = cs.getD q 0 then vs.getD q' 0 else 0)) =
      ∑ q' ∈ range vs.length, (if t0.tgt (cs.getD q' 0) = j then vs.getD q' 0 else 0) := by
    refine Finset.sum_congr rfl fun q' hq' => ?_
    by_cases ht : t0.tgt (cs.getD q' 0) = j
    · rw [ite_eq_left ht, ite_eq_left ((hiff q' (Finset.mem_range.1 hq')).1 ht)]
    · rw [ite_eq_right ht, ite_eq_right fun he => ht ((hiff q' (Finset.mem_range.1 hq')).2 he)]
  have hcard : ((range vs.length).filter fun q' => cs.getD q' 0 = cs.getD q 0) =
      (range vs.length).filter fun q' => t0.tgt (cs.getD q' 0) = j :=
    Finset.filter_congr fun q' hq' => (hiff q' (Finset.mem_range.1 hq')).symm
  rw [hsum, hcard]
  have e2 : ((routeR vs cs (toRTo t0 offs).1).leaves.getD j dLeafR).2.1 = offs.getD j 0 +
      ∑ q' ∈ range vs.length, (if t0.tgt (cs.getD q' 0) = j then vs.getD q' 0 else 0) := by
    rw [h2]
  have e3 : ((routeR vs cs (toRTo t0 offs).1).leaves.getD j dLeafR).2.2.1 =
      ((range vs.length).filter fun q' => t0.tgt (cs.getD q' 0) = j).card := by
    rw [h3, Finset.card_filter]; simp
  rw [← e2, ← e3]
  exact hmod

/-- **The offset check**: route the fields by class from the class tree with leaf offsets `offs`, test every class
mod `p` (offset `h = 2^(b-1)` per field). -/
noncomputable def checkKRo (p b : ℕ) (slices : List SInt) (cls : List ℕ) (t0 : AT) (offs : List ℕ) : Bool :=
  RT.okMod p (Nat.shiftLeft 1 (Nat.sub b 1)) (routeR (fieldsK b slen (offL b slen) slices) cls (toRTo t0 offs).1)

/-- **Soundness of the offset check**: offset of the class plus the class sum of `F` is `0 mod p`. -/
theorem checkKRo_sound (p b : ℕ) (hb : 0 < b) (slices : List SInt) (cls : List ℕ) (t0 : AT) (offs : List ℕ)
    (h : checkKRo p b slices cls t0 offs = true) (F : ℕ → ℕ → ℕ → ℕ → ℤ)
    (hS : ∀ w3 < 24, gv slices w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      F w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2))
    (hF : ∀ q < 24 * slen, |F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2| < 2 ^ (b - 1))
    (hcls : cls.length = 24 * slen) (q : ℕ) (hq : q < 24 * slen) :
    (offs.getD (t0.tgt (cls.getD q 0)) 0 : ℤ) + (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0)) ≡ 0 [ZMOD p] := by
  set vs := fieldsK b slen (offL b slen) slices with hvs
  have hvl : vs.length = 24 * slen := fieldsK_length b slices
  have hlen : vs.length = cls.length := by rw [hvl, hcls]
  have hsound := okMod_sound_off p (Nat.shiftLeft 1 (Nat.sub b 1)) vs cls t0 offs h hlen q (by rw [hvl]; exact hq)
  rw [hvl] at hsound
  set H : ℕ := Nat.shiftLeft 1 (Nat.sub b 1) with hH
  have hH0 : H = 2 ^ (b - 1) := by
    rw [hH, show Nat.shiftLeft 1 (Nat.sub b 1) = 1 <<< (b - 1) from rfl, Nat.one_shiftLeft]
  have hH' : (H : ℤ) = 2 ^ (b - 1) := by rw [hH0]; push_cast; ring
  have hval : ∀ q' ∈ range (24 * slen), ((vs.getD q' 0 : ℕ) : ℤ) =
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 + 2 ^ (b - 1) := by
    intro q' hq'
    have hq'' := Finset.mem_range.1 hq'
    rw [hvs, fieldsK_val b hb slices F hS hF q' hq'']
    unfold fld
    have := abs_lt.1 (hF q' hq'')
    rw [Int.toNat_of_nonneg (by linarith)]
  set S := ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
    F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) with hSdef
  set cnt := ((range (24 * slen)).filter fun q' => cls.getD q' 0 = cls.getD q 0).card with hcnt
  set o : ℕ := offs.getD (t0.tgt (cls.getD q 0)) 0 with ho
  have hsum : ((o + ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then vs.getD q' 0 else 0) : ℕ) : ℤ) =
      (o : ℤ) + S + cnt * 2 ^ (b - 1) := by
    push_cast
    rw [hSdef, hcnt, Finset.card_filter, Nat.cast_sum, Finset.sum_mul, add_assoc, ← Finset.sum_add_distrib]
    refine congrArg (fun x => (o : ℤ) + x) ?_
    refine Finset.sum_congr rfl fun q' hq' => ?_
    split_ifs with hc
    · rw [hval q' hq']; push_cast; ring
    · push_cast; ring
  have hmod : ((o + ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then vs.getD q' 0 else 0) : ℕ) : ℤ) ≡
      ((cnt * H : ℕ) : ℤ) [ZMOD p] := by
    rw [Int.ModEq]; exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) hsound
  rw [hsum] at hmod
  push_cast at hmod
  rw [hH'] at hmod
  have hmod' : (o : ℤ) + S + (cnt : ℤ) * 2 ^ (b - 1) ≡ 0 + (cnt : ℤ) * 2 ^ (b - 1) [ZMOD p] := by
    rw [zero_add]; exact hmod
  exact Int.ModEq.add_right_cancel' _ hmod'

/-! ### Slices of a subset of the parts -/

/-- The rule-group parts of `gs`, data mod `p` (the first parts of `famPartsMod`). -/
def gpartsMod (p zmul : ℕ) (C : CertD) (gs : List GrpF) : List Part :=
  gs.map fun G => ⟨ruleSpecF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) G.kpos G.lpos, G.tree⟩

/-- Packed slices of the rule groups `gts` (row-form leaves `lr`) and the parts `others`, data mod `p`
(`slicesKRB p zmul C f gts lr zs za eqT b = slicesG p zmul C gts lr b (otherPartsModB p zmul C f zs za eqT)`). -/
noncomputable def slicesG (p zmul : ℕ) (C : CertD) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (b : ℕ) (others : List Part) : List SInt :=
  addLR (foldrR (fun Gt acc => addLR (evalTreeRR (certModR p zmul C) Gt.1.kpos Gt.1.lpos Gt.2 lr b Gt.1.tree) acc) [] gts)
    (foldrR (fun P acc => addLR (evalTree P.S b P.tree) acc) [] others)

lemma slicesG_eq (p zmul : ℕ) (C : CertD) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr) (b : ℕ) (others : List Part) :
    slicesG p zmul C gts lr b others =
      addL (partsSlices b (grpPartsRows (certModR p zmul C) gts lr)) (partsSlices b others) := by
  unfold slicesG partsSlices grpPartsRows
  rw [addLR_eq, foldrR_eq, foldrR_eq, List.map_map, List.foldr_map, List.foldr_map]
  congr 1
  · refine congrArg (fun g => List.foldr g [] gts) (funext fun Gt => funext fun acc => ?_)
    rw [addLR_eq, evalTreeRR_eq _ _ _ _ lr b hlr]
    rfl
  · refine congrArg (fun g => List.foldr g [] _) (funext fun P => funext fun acc => ?_)
    rw [addLR_eq]

/-- **The packed word values of a subset of the parts.** -/
theorem slicesG_gv (p zmul : ℕ) (C : CertD) (gts : List (GrpF × List (List (List SInt))))
    (htab : ∀ Gt ∈ gts, Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (b : ℕ) (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr)
    (hleaf : ∀ d0 d1 d2 d3 items k, gv (lr d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (others : List Part) (hO : ∀ P ∈ others, ∀ m, (P.S.rows m).length = 24) (w3 : ℕ) (hw : w3 < 24) :
    gv (slicesG p zmul C gts lr b others) w3 =
      ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
        partsF (gpartsMod p zmul C (gts.map Prod.fst) ++ others) w0 w1 w2 w3 * 2 ^ (b * w0)) *
          2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  have hC : certModR p zmul C = certMod p zmul C := certModR_eq p zmul C
  have hmods : (certMod p zmul C).mods = C.mods := rfl
  have hrowsR : ∀ Gt ∈ gts, ∀ m, (specRows (certMod p zmul C) Gt.1.kpos Gt.1.lpos Gt.2 lr).rows m =
      localRowsF ((certMod p zmul C).mods.getD m default) Gt.1.kpos Gt.1.lpos := by
    intro Gt hGt m
    simp only [specRows]
    rw [htab Gt hGt, mkTab_eq, getD_map', hmods]
  rw [slicesG_eq p zmul C gts lr hlr b others, gv_addL, hC]
  have hrowsA : ∀ P ∈ grpPartsRows (certMod p zmul C) gts lr, ∀ m, (P.S.rows m).length = 24 := by
    intro P hP m
    simp only [grpPartsRows, List.mem_map] at hP
    obtain ⟨Gt, hGt, rfl⟩ := hP
    rw [hrowsR Gt hGt m]
    exact localRowsF_length _ _ _
  rw [partsSlices_gv b _ hrowsA w3 hw, partsSlices_gv b _ hO w3 hw, pack_add]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun w1 _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun w0 _ => ?_
  congr 1
  rw [partsF_append]
  refine congrArg (· + partsF others w0 w1 w2 w3) ?_
  unfold grpPartsRows gpartsMod
  rw [partsF_map, partsF_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun Gt hGt => ?_)
  simp only [Function.comp_apply]
  refine specTree_eq_of_leaf (specRows (certMod p zmul C) Gt.1.kpos Gt.1.lpos Gt.2 lr)
    (ruleSpecF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) Gt.1.kpos Gt.1.lpos)
    (by funext m; rw [hrowsR Gt hGt m]; rfl) rfl (fun m1 m2 m3 lf k => hleaf _ _ _ _ _ k) _ _ _ _ _

/-! ### Combining the declarations -/

lemma sum_map_modEq_zero {β : Type} (p : ℕ) (g : β → ℤ) :
    ∀ (L : List β), (∀ s ∈ L, g s ≡ 0 [ZMOD p]) → (L.map g).sum ≡ 0 [ZMOD p]
  | [], _ => by simp only [List.map_nil, List.sum_nil]; exact Int.ModEq.rfl
  | s :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    have h1 := h s List.mem_cons_self
    have h2 := sum_map_modEq_zero p g L (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))
    simpa using h1.add h2

lemma sum_map_ite {β : Type} (R : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] (G : β → ℕ → ℤ) :
    ∀ (L : List β), (L.map fun s => ∑ q' ∈ R, (if c q' then G s q' else 0)).sum =
      ∑ q' ∈ R, (if c q' then (L.map fun s => G s q').sum else 0)
  | [] => by simp
  | s :: L => by
    simp only [List.map_cons, List.sum_cons]
    rw [sum_map_ite R c G L, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q' _ => ?_
    split_ifs <;> simp

/-- **Split check, one modulus**: if every declaration `s ∈ sp` (rule groups `s.1`, other parts `s.2.1`, leaf offsets
`s.2.2`) passes `checkKRo`, the offsets sum to `0 mod p` leafwise, and the declarations' parts add up to
`famPartsMod`, then every class sum of `famParts` is `0 mod p`. -/
theorem classSums_modP_split (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) (hb : 0 < b)
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr)
    (hleaf : ∀ d0 d1 d2 d3 items k, gv (lr d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (cls : List ℕ) (hcls : cls.length = 24 * slen) (t0 : AT)
    (sp : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ))
    (htab : ∀ s ∈ sp, ∀ Gt ∈ s.1,
      Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (hO : ∀ s ∈ sp, ∀ P ∈ s.2.1, ∀ m, (P.S.rows m).length = 24)
    (hF : ∀ s ∈ sp, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3| < 2 ^ (b - 1))
    (hchk : ∀ s ∈ sp, checkKRo p b (slicesG p zmul C s.1 lr b s.2.1) cls t0 s.2.2 = true)
    (hoff : ∀ i < t0.leaves.length, (sp.map fun s => s.2.2.getD i 0).sum % p = 0)
    (hall : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      (sp.map fun s => partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3).sum =
        partsF (famPartsMod p zmul C f gs zs za eqT) w0 w1 w2 w3)
    (q : ℕ) (hq : q < 24 * slen) :
    (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF (famParts C zmul f gs zs za eqT) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2
      else 0)) ≡ 0 [ZMOD p] := by
  have h24 : ∀ x : ℕ, x % 24 < 24 := fun x => Nat.mod_lt _ (by norm_num)
  have hwd : ∀ q' < 24 * slen, (wd q').2.2.2 < 24 := by
    intro q' hq'; unfold wd slen at *; simp only; omega
  have hj : t0.tgt (cls.getD q 0) < t0.leaves.length := AT.tgt_lt t0 _
  -- each declaration: its offset plus its class sum is `0 mod p`
  have hdecl : ∀ s ∈ sp, ((s.2.2.getD (t0.tgt (cls.getD q 0)) 0 : ℕ) : ℤ) +
      (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
        partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2
        else 0)) ≡ 0 [ZMOD p] := by
    intro s hs
    exact checkKRo_sound p b hb _ cls t0 s.2.2 (hchk s hs) _
      (slicesG_gv p zmul C s.1 (htab s hs) b lr hlr hleaf s.2.1 (hO s hs))
      (fun q' hq' => hF s hs _ _ _ _ (h24 _) (h24 _) (h24 _) (hwd q' hq')) hcls q hq
  have hsumd := sum_map_modEq_zero p _ sp hdecl
  rw [List.sum_map_add] at hsumd
  -- the offsets sum to `0 mod p`
  have hoffZ : (sp.map fun s => ((s.2.2.getD (t0.tgt (cls.getD q 0)) 0 : ℕ) : ℤ)).sum ≡ 0 [ZMOD p] := by
    have h := hoff _ hj
    have hc : (((sp.map fun s => s.2.2.getD (t0.tgt (cls.getD q 0)) 0).sum : ℕ) : ℤ) =
        (sp.map fun s => ((s.2.2.getD (t0.tgt (cls.getD q 0)) 0 : ℕ) : ℤ)).sum := by
      rw [Nat.cast_list_sum, List.map_map]; rfl
    rw [← hc, Int.ModEq, ← Int.natCast_mod, h]
    rfl
  -- the class sums add up to the class sum of `famPartsMod`
  rw [sum_map_ite] at hsumd
  have hcs : (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      (sp.map fun s => partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1)
        (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2).sum else 0)) =
      ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
        partsF (famPartsMod p zmul C f gs zs za eqT) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) := by
    refine Finset.sum_congr rfl fun q' hq' => ?_
    split_ifs
    · exact hall _ _ _ _ (h24 _) (h24 _) (h24 _) (hwd q' (Finset.mem_range.1 hq'))
    · rfl
  rw [hcs] at hsumd
  have hmodP : (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF (famPartsMod p zmul C f gs zs za eqT) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0))
      ≡ 0 [ZMOD p] := by
    have h2 := (Int.ModEq.add_right (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF (famPartsMod p zmul C f gs zs za eqT) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0))
      hoffZ).symm.trans hsumd
    simpa using h2
  refine Int.ModEq.trans ?_ hmodP
  refine Int.ModEq.sum fun q' _ => ?_
  split_ifs
  · exact partsF_mod p zmul C f gs zs za eqT _ _ _ _
  · exact Int.ModEq.rfl

/-- The parts of a two-way split (groups `gtsA`; groups `gtsB` with the objective and the λ-box equality parts) add
up to `famPartsMod`. -/
theorem hall_two (p zmul : ℕ) (C : CertD) (f : ℕ) (gtsA gtsB : List (GrpF × List (List (List SInt))))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (offsA offsB : List ℕ) (w0 w1 w2 w3 : ℕ)
    (h0 : w0 < 24) (h1 : w1 < 24) (h2 : w2 < 24) (h3 : w3 < 24) :
    ([(gtsA, ([] : List Part), offsA), (gtsB, otherPartsModB p zmul C f zs za eqT, offsB)].map fun s =>
      partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3).sum =
      partsF (famPartsMod p zmul C f ((gtsA ++ gtsB).map Prod.fst) zs za eqT) w0 w1 w2 w3 := by
  have he : partsF (eqBoxPartsF (certModR p zmul C) f eqT) w0 w1 w2 w3 =
      partsF (eqPartsF (certMod p zmul C) f eqT) w0 w1 w2 w3 := by
    rw [certModR_eq]; exact partsF_eqBox (certMod p zmul C) f eqT ⟨w0, h0⟩ ⟨w1, h1⟩ ⟨w2, h2⟩ ⟨w3, h3⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.append_nil]
  unfold famPartsMod otherPartsModB gpartsMod
  rw [List.map_append, List.map_append]
  simp only [partsF_append]
  rw [he]
  ring


/-- **`hsum_of_checks` for split declarations**: for every modulus `p ∈ ps` some list of declarations `sp` (rule
groups, other parts, leaf offsets) passes `checkKRo`, with offsets summing to `0 mod p` leafwise, word bounds per
declaration, and parts adding up to `famPartsMod`. -/
theorem hsum_of_checks_split (d : ℕ) (types : List TypeD) (mods : List ModD) (eqs : List EqGroupD)
    (Z : List NPT.Cert.PBlock) (Lden : ℕ) (hd : 0 < d) (hL : 0 < Lden) (zmul f b : ℕ) (hb : 0 < b) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul G = true)
    (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f))
    (zs za : Fin 24 → ℤ)
    (hzs : ∀ p, (zs p : ℚ) = 2 * Matrix.trace (VG ℚ d 0 p) - Matrix.trace (VG ℚ d 0 21 * VG ℚ d 0 p))
    (hza : ∀ p, (za p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p))
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heq : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
      (eqT (P.specs.getD l.val default) (nfN d l.val) p o : ℚ) =
        CertD.eqLoc ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ (P.specs.getD l.val default) (nf 3 d l) p o)
    (lr : ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : ∀ p, LRShape (lr p))
    (hleaf : ∀ p d0 d1 d2 d3 items k, gv (lr p d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩) 1
        (-(den3 d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
    (B : ℕ) (hB : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famParts ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul f gs zs za eqT) w0 w1 w2 w3| ≤ B)
    (hBp : 24 * slen * B < ps.prod)
    (cls : List ℕ) (hcls : cls.length = 24 * slen) (t0 : AT)
    (hsplit : ∀ p ∈ ps, ∃ sp : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ),
      (∀ s ∈ sp, ∀ Gt ∈ s.1, Gt.2 = mkTab ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ Gt.1.kpos Gt.1.lpos
        (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos)) ∧
      (∀ s ∈ sp, ∀ P ∈ s.2.1, ∀ m, (P.S.rows m).length = 24) ∧
      (∀ s ∈ sp, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
        |partsF (gpartsMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ (s.1.map Prod.fst) ++ s.2.1)
          w0 w1 w2 w3| < 2 ^ (b - 1)) ∧
      (∀ s ∈ sp, checkKRo p b (slicesG p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ s.1 (lr p) b s.2.1)
        cls t0 s.2.2 = true) ∧
      (∀ i < t0.leaves.length, (sp.map fun s => s.2.2.getD i 0).sum % p = 0) ∧
      (∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
        (sp.map fun s => partsF (gpartsMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ (s.1.map Prod.fst) ++
          s.2.1) w0 w1 w2 w3).sum =
          partsF (famPartsMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f gs zs za eqT) w0 w1 w2 w3))
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls.getD (posW w) 0 = cls.getD (posW w₀) 0),
      CertD.Λ ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f w = 0 := by
  refine hsum_of_posSums d types mods eqs Z Lden hd hL zmul f gs hG hperm zs za hzs hza eqT heq cls
    (fun q hq => ?_) w₀
  refine eq_zero_of_modEq_list _ ps hcop (fun p hp => ?_)
    (lt_of_le_of_lt (classSum_abs_le cls _ B hB q) hBp)
  obtain ⟨sp, htab, hO, hF, hchk, hoff, hall⟩ := hsplit p hp
  exact classSums_modP_split p zmul _ f gs zs za eqT b hb (lr p) (hlr p) (hleaf p) cls hcls t0 sp htab hO hF hchk
    hoff hall q hq


lemma partsF_nil (w0 w1 w2 w3 : ℕ) : partsF [] w0 w1 w2 w3 = 0 := by simp [partsF]

lemma sum_parts_split (p zmul : ℕ) (C : CertD) (w0 w1 w2 w3 : ℕ) :
    ∀ (sp : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ)),
    (sp.map fun s => partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3).sum =
      partsF (gpartsMod p zmul C ((sp.map (·.1)).flatten.map Prod.fst)) w0 w1 w2 w3 +
        partsF ((sp.map (·.2.1)).flatten) w0 w1 w2 w3
  | [] => by simp [gpartsMod, partsF_nil]
  | s :: sp => by
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.map_append]
    rw [sum_parts_split p zmul C w0 w1 w2 w3 sp]
    unfold gpartsMod
    rw [List.map_append]
    simp only [partsF_append]
    ring

/-- **Any split adds up**: if the declarations' rule groups concatenate to `gts` and their other parts to the objective
and λ-box equality parts, the declarations' parts add up to `famPartsMod`. -/
theorem hall_split (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (sp : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ))
    (hg : (sp.map (·.1)).flatten = gts) (ho : (sp.map (·.2.1)).flatten = otherPartsModB p zmul C f zs za eqT)
    (w0 w1 w2 w3 : ℕ) (h0 : w0 < 24) (h1 : w1 < 24) (h2 : w2 < 24) (h3 : w3 < 24) :
    (sp.map fun s => partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3).sum =
      partsF (famPartsMod p zmul C f (gts.map Prod.fst) zs za eqT) w0 w1 w2 w3 := by
  have he : partsF (eqBoxPartsF (certModR p zmul C) f eqT) w0 w1 w2 w3 =
      partsF (eqPartsF (certMod p zmul C) f eqT) w0 w1 w2 w3 := by
    rw [certModR_eq]; exact partsF_eqBox (certMod p zmul C) f eqT ⟨w0, h0⟩ ⟨w1, h1⟩ ⟨w2, h2⟩ ⟨w3, h3⟩
  rw [sum_parts_split, hg, ho]
  unfold famPartsMod otherPartsModB gpartsMod
  simp only [partsF_append]
  rw [he]
  ring


end NPT.Cert.KR
