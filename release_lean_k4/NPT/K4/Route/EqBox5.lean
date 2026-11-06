/-
NPT.K4.Route.EqBox5 — the equality parts of a family on an aux slice as one λ-box per (group, part).

Legs 0..3 carry the rows `o ↦ eqLocF spec_l 3 p o` (`o < lamN lam l`); the leaf is the λ-tensor contracted at the
auxiliary leg, entry `(o0, o1, o2, o3) ↦ Σ_{entries} c · λ · eqLocF spec_4 2 w4 o4`, built by one array fold over the
entries (`accumW`, linear in the number of entries).  The boxes have the word values of the rank-one parts
`eqParts5` (`partsF_eqBox5`), hence the equality component of `D · ΛS` (`eq_component5B`).  As EP_3's `EqBox`
(`specTree_eqBox`), with the leaf weight `c · λ · eqLocF spec_4 2 w4 o4`.
-/
import NPT.K4.Route.Assembly5
import NPT.Cert.Ident.EqBox

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.Brauer NPT.K4

/-! ### Accumulation by an array fold -/

/-- `wt ol` added at index `enc ol` for every entry, starting from `N` zeros. -/
def accumW (N : ℕ) (enc : List ℕ × ℤ → ℕ) (wt : List ℕ × ℤ → ℤ) (lam : List (List ℕ × ℤ)) : Array ℤ :=
  lam.foldl (fun a ol => a.modify (enc ol) (· + wt ol)) (Array.replicate N 0)

lemma getD_modify_add (l : List ℤ) (i k : ℕ) (v : ℤ) (hk : k < l.length) :
    (l.modify i (· + v)).getD k 0 = l.getD k 0 + (if i = k then v else 0) := by
  have hk' : k < (l.modify i (· + v)).length := by simpa using hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some, List.getElem_modify,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  split_ifs <;> simp

lemma foldl_modify_size (enc : List ℕ × ℤ → ℕ) (wt : List ℕ × ℤ → ℤ) :
    ∀ (lam : List (List ℕ × ℤ)) (acc : Array ℤ),
      (lam.foldl (fun a ol => a.modify (enc ol) (· + wt ol)) acc).size = acc.size
  | [], acc => rfl
  | ol :: lam, acc => by
    rw [List.foldl_cons, foldl_modify_size enc wt lam, Array.size_modify]

lemma foldl_modify_getD (enc : List ℕ × ℤ → ℕ) (wt : List ℕ × ℤ → ℤ) :
    ∀ (lam : List (List ℕ × ℤ)) (acc : Array ℤ) (k : ℕ), k < acc.size →
      (lam.foldl (fun a ol => a.modify (enc ol) (· + wt ol)) acc).toList.getD k 0 =
        acc.toList.getD k 0 + (lam.map fun ol => if enc ol = k then wt ol else 0).sum
  | [], acc, k, _ => by simp
  | ol :: lam, acc, k, hk => by
    rw [List.foldl_cons, foldl_modify_getD enc wt lam _ k (by rw [Array.size_modify]; exact hk),
      Array.toList_modify, getD_modify_add _ _ _ _ (by rw [Array.length_toList]; exact hk)]
    simp only [List.map_cons, List.sum_cons]
    ring

lemma accumW_size (N : ℕ) (enc : List ℕ × ℤ → ℕ) (wt : List ℕ × ℤ → ℤ) (lam : List (List ℕ × ℤ)) :
    (accumW N enc wt lam).size = N := by
  unfold accumW; rw [foldl_modify_size, Array.size_replicate]

lemma accumW_getD (N : ℕ) (enc : List ℕ × ℤ → ℕ) (wt : List ℕ × ℤ → ℤ) (lam : List (List ℕ × ℤ)) (k : ℕ)
    (hk : k < N) :
    (accumW N enc wt lam).toList.getD k 0 = (lam.map fun ol => if enc ol = k then wt ol else 0).sum := by
  unfold accumW
  rw [foldl_modify_getD enc wt lam _ k (by rw [Array.size_replicate]; exact hk), Array.toList_replicate,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_eq_left hk, Option.getD_some, zero_add]

lemma gv_map_ofInt (l : List ℤ) (k : ℕ) (hk : k < l.length) : gv (l.map SInt.ofInt) k = l.getD k 0 := by
  unfold gv
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some,
    Option.getD_some, SInt.val_ofInt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

/-! ### The λ-box of one part on an aux slice -/

/-- Leaf weight of an entry: `c · λ · eqLocF spec_4 2 w4 o4`. -/
def eqWt5 (C : CertD) (P : EqPartD) (c : ℤ) (w4 : Fin 24) (ol : List ℕ × ℤ) : ℤ :=
  c * ol.2 * eqLocF C (P.specs.getD 4 default) 2 w4 (ol.1.getD 4 0)

/-- The λ-tensor of part `P` contracted at the auxiliary leg. -/
def eqLeaf5 (C : CertD) (g : EqGroupD) (P : EqPartD) (c : ℤ) (w4 : Fin 24) : List SInt :=
  (accumW (lamN g.lam 0 * (lamN g.lam 1 * (lamN g.lam 2 * lamN g.lam 3)))
    (fun ol => enc4 (lamN g.lam 1) (lamN g.lam 2) (lamN g.lam 3) ol.1) (eqWt5 C P c w4) g.lam).toList.map
    SInt.ofInt

def eqBoxSpec5 (C : CertD) (g : EqGroupD) (P : EqPartD) (c : ℤ) (w4 : Fin 24) : Spec where
  rows m := eqRows (eqLocF C) (P.specs.getD m default) 3 (lamN g.lam m)
  dimsq m := lamN g.lam m
  leaf _ _ _ _ := eqLeaf5 C g P c w4

def eqBoxPart5 (C : CertD) (g : EqGroupD) (P : EqPartD) (c : ℤ) (w4 : Fin 24) : Part :=
  ⟨eqBoxSpec5 C g P c w4, rank1Tree⟩

/-- The equality parts of family `f` on the slice `w4`, one λ-box per (group, part). -/
def eqBoxParts5 (C : CertD) (f : ℕ) (cE : ℤ) (w4 : Fin 24) : List Part :=
  C.eqs.flatMap fun g => g.parts.flatMap fun P => if P.fam = f then [eqBoxPart5 C g P (-(P.sign) * cE) w4] else []

/-- **The λ-box has the word values of the rank-one parts.** -/
theorem specTree_eqBox5 (C : CertD) (g : EqGroupD) (P : EqPartD) (c : ℤ) (w4 : Fin 24) (w0 w1 w2 w3 : Fin 24) :
    specTree (eqBoxSpec5 C g P c w4) rank1Tree w0.val w1.val w2.val w3.val =
      (g.lam.map fun ol => specTree (rank1Spec (fun l p => eqLocF C (P.specs.getD l default) 3 p (ol.1.getD l 0))
        (eqWt5 C P c w4 ol)) rank1Tree w0.val w1.val w2.val w3.val).sum := by
  simp only [rank1_spec]
  rw [specTree_paths]
  simp only [rank1Tree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, boxF]
  have hd : ∀ m, (eqBoxSpec5 C g P c w4).dimsq m = lamN g.lam m := fun _ => rfl
  simp only [hd]
  set N1 := lamN g.lam 1 with hN1
  set N2 := lamN g.lam 2 with hN2
  set N3 := lamN g.lam 3 with hN3
  set N0 := lamN g.lam 0 with hN0
  -- rows and leaf entries
  have hrow : ∀ (m : ℕ) (w : Fin 24) (o : ℕ), o < lamN g.lam m →
      aval ((eqBoxSpec5 C g P c w4).rows m) w.val o = eqLocF C (P.specs.getD m default) 3 w o :=
    fun m w o ho => aval_eqRows (eqLocF C) _ _ _ w o ho
  have hleaf : ∀ i0 i1 i2 i3, i0 < N0 → i1 < N1 → i2 < N2 → i3 < N3 →
      gv ((eqBoxSpec5 C g P c w4).leaf 1 2 3 ⟨0, []⟩)
          (i0 * (N1 * N2 * N3) + (i1 * (N2 * N3) + (i2 * N3 + i3))) =
        (g.lam.map fun ol => if enc4 N1 N2 N3 ol.1 =
          ((i0 * N1 + i1) * N2 + i2) * N3 + i3 then eqWt5 C P c w4 ol else 0).sum := by
    intro i0 i1 i2 i3 h0 h1 h2 h3
    have hk : i0 * (N1 * N2 * N3) + (i1 * (N2 * N3) + (i2 * N3 + i3)) =
        ((i0 * N1 + i1) * N2 + i2) * N3 + i3 := by ring
    have hlt : ((i0 * N1 + i1) * N2 + i2) * N3 + i3 < N0 * (N1 * (N2 * N3)) := by
      have := mr4_lt N0 N1 N2 N3 i0 i1 i2 i3 h0 h1 h2 h3
      unfold mr4 at this
      rw [show N0 * (N1 * (N2 * N3)) = N0 * N1 * N2 * N3 by ring]
      exact this
    have hlen : ((i0 * N1 + i1) * N2 + i2) * N3 + i3 <
        (accumW (N0 * (N1 * (N2 * N3))) (fun ol => enc4 N1 N2 N3 ol.1) (eqWt5 C P c w4) g.lam).toList.length := by
      rw [Array.length_toList, accumW_size]; exact hlt
    show gv (eqLeaf5 C g P c w4) _ = _
    unfold eqLeaf5
    rw [hk, gv_map_ofInt _ _ hlen, accumW_getD _ _ _ _ _ hlt]
  rw [Finset.sum_congr rfl fun i0 hi0 => Finset.sum_congr rfl fun i1 hi1 => Finset.sum_congr rfl fun i2 hi2 =>
    Finset.sum_congr rfl fun i3 hi3 => by
      rw [hrow 0 w0 i0 (Finset.mem_range.1 hi0), hrow 1 w1 i1 (Finset.mem_range.1 hi1),
        hrow 2 w2 i2 (Finset.mem_range.1 hi2), hrow 3 w3 i3 (Finset.mem_range.1 hi3),
        hleaf i0 i1 i2 i3 (Finset.mem_range.1 hi0) (Finset.mem_range.1 hi1) (Finset.mem_range.1 hi2)
          (Finset.mem_range.1 hi3)]]
  -- exchange the list sum outward, then evaluate the indicator entry by entry
  simp only [mul_list_sum, sum_list1]
  refine congrArg List.sum (List.map_congr_left fun ol hol => ?_)
  exact box_indicator _ _ _ _ (fun i => eqLocF C (P.specs.getD 0 default) 3 w0 i)
    (fun i => eqLocF C (P.specs.getD 1 default) 3 w1 i) (fun i => eqLocF C (P.specs.getD 2 default) 3 w2 i)
    (fun i => eqLocF C (P.specs.getD 3 default) 3 w3 i) ol.1 (eqWt5 C P c w4 ol)
    (lt_lamN g.lam 0 ol hol) (lt_lamN g.lam 1 ol hol) (lt_lamN g.lam 2 ol hol) (lt_lamN g.lam 3 ol hol)

/-- **The λ-boxes of a family on a slice have the word values of its rank-one equality parts.** -/
theorem partsF_eqBox5 (C : CertD) (f : ℕ) (cE : ℤ) (w4 w0 w1 w2 w3 : Fin 24) :
    partsF (eqBoxParts5 C f cE w4) w0.val w1.val w2.val w3.val =
      partsF (eqParts5 C f cE w4) w0.val w1.val w2.val w3.val := by
  unfold eqBoxParts5 eqParts5
  rw [partsF_flatMap, partsF_flatMap]
  refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
  rw [partsF_flatMap, partsF_flatMap]
  refine congrArg List.sum (List.map_congr_left fun P _ => ?_)
  split_ifs with hf
  · simp only [partsF, eqBoxPart5, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.map_map]
    rw [specTree_eqBox5]
    rfl
  · rfl

/-- **Equality component of `D · ΛS` from the λ-boxes** (as `eq_component5`). -/
theorem eq_component5B (C : CertD) (hk : C.k = 4) (hd3 : C.d = 3) (f : ℕ) (cE : ℤ) (D : ℚ)
    (hcE : (cE : ℚ) = D / C.lamDen)
    (hkind : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, ∀ l : Fin (C.k + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf C.k C.d l = 2)
    (w : Fin (C.k + 1) → Fin 24) :
    ((partsF (eqBoxParts5 C f cE (w 4)) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
      -D * (C.eqs.map fun g => (g.parts.map fun P =>
        if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum).sum := by
  rw [partsF_eqBox5]
  exact eq_component5 C hk hd3 f cE D hcE hkind w

lemma eqBoxParts5_rows (C : CertD) (f : ℕ) (cE : ℤ) (w4 : Fin 24) :
    ∀ P ∈ eqBoxParts5 C f cE w4, ∀ m, (P.S.rows m).length = 24 := by
  intro P hP m
  unfold eqBoxParts5 at hP
  simp only [List.mem_flatMap] at hP
  obtain ⟨g, _, P', _, hP'⟩ := hP
  split_ifs at hP' with hf
  · rw [List.mem_singleton] at hP'
    subst hP'
    simp [eqBoxPart5, eqBoxSpec5, eqRows]
  · simp at hP'

end NPT.K4.Route

#print axioms NPT.K4.Route.eq_component5B
