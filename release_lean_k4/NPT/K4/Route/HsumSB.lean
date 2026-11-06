/-
NPT.K4.Route.HsumSB — the evaluated parts of family `f` on an aux slice (rule groups, objective and trace rank-one parts,
λ-boxes `eqBoxParts5`), the assembly `ΛS · D = partsF (parts5B …)`, and the class sums from the 24 slice checks.
Same as `ΛS_partsF5` / `hsum_of_slices`, with the λ entries packed into one box per (group, part) (`EqBox5`).
-/
import NPT.K4.Route.HsumS
import NPT.K4.Route.EqBox5

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.K4

/-- All parts of family `f` on the slice `w4`, with the λ parts as boxes. -/
def parts5B (C : CertD) (α β : ℕ) (cG cO cT cE : ℤ) (f : ℕ) (gs : List GrpF) (w4 : Fin 24) : List Part :=
  gs.map (slicePart C cG w4.val) ++
    (if f = 0 then [rank1Part (fun _ p => zsTt α β p) (cO * zaT5 w4),
      rank1Part (fun _ p => tsT5 p) (cT * taT5 w4)] else []) ++
    eqBoxParts5 C f cE w4

/-- **Assembly on a slice, λ-boxes.** -/
theorem ΛS_partsF5B (C : CertD) (hk : C.k = 4) (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α) (nu : ℚ) (E0 : ℕ)
    (cG cO cT cE : ℤ) (D : ℚ) (f : ℕ) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK5 C E0 G = true) (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems C f))
    (hcG : (cG : ℚ) * 2 ^ E0 = -D)
    (hcO : (cO : ℚ) = D / ((α : ℚ) ^ 4 * (2 * 3 ^ 4) ^ 4))
    (hcT : (cT : ℚ) = -(D * nu / (2 * 3 ^ 4) ^ 4))
    (hcE : (cE : ℚ) = D / C.lamDen)
    (hkind : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, ∀ l : Fin (C.k + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf C.k C.d l = 2)
    (w : Fin (C.k + 1) → Fin 24) :
    ΛS C α β nu f w * D =
      ((partsF (parts5B C α β cG cO cT cE f gs (w 4)) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) := by
  rw [ΛS_partsF5 C hk hd3 α β hα nu E0 cG cO cT cE D f gs hG hperm hcG hcO hcT hcE hkind w]
  unfold parts5 parts5B
  rw [partsF_append, partsF_append, Int.cast_add, Int.cast_add, eq_component5 C hk hd3 f cE D hcE hkind w,
    partsF_append, partsF_append, Int.cast_add, Int.cast_add, eq_component5B C hk hd3 f cE D hcE hkind w]

/-- **Class sums from the slice checks (λ-boxes).** -/
theorem hsum_of_slicesB (d : ℕ) (types : List TypeD) (mods : List ModD) (eqs : List EqGroupD)
    (Z : List NPT.Cert.PBlock) (Lden lamDen : ℕ) (hd3 : d = 3) (α β : ℕ) (hα : 0 < α) (nu : ℚ) (E0 : ℕ)
    (cG cO cT cE : ℤ) (D : ℚ) (hD : D ≠ 0) (f : ℕ) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK5 ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ E0 G = true)
    (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ f))
    (hcG : (cG : ℚ) * 2 ^ E0 = -D)
    (hcO : (cO : ℚ) = D / ((α : ℚ) ^ 4 * (2 * 3 ^ 4) ^ 4))
    (hcT : (cT : ℚ) = -(D * nu / (2 * 3 ^ 4) ^ 4))
    (hcE : (cE : ℚ) = D / lamDen)
    (hkind : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (4 + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf 4 d l = 2)
    (b : ℕ) (clsL : ℕ → List ℕ) (tL : ℕ → AT)
    (hchk : ∀ j : Fin 24, sliceCheck b (parts5B ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ α β cG cO cT cE f gs j)
      (clsL j.val) (tL j.val) = true)
    (c : ℕ) (hkey : ∀ j : Fin 24, ((tL j.val).leaves.getD ((tL j.val).tgt c) dLeaf).1 = c)
    (Rint : ℤ) (hoff : ∑ j : Fin 24, offAt (tL j.val) c = -Rint) :
    ∑ w ∈ univ.filter (fun w : Fin (4 + 1) → Fin 24 => cls5 clsL w = c),
      ΛS ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ α β nu f w = (Rint : ℚ) / D := by
  set C : CertD := ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ with hC
  have key : ∀ w : Fin (4 + 1) → Fin 24, ΛS C α β nu f w =
      ((partsF (parts5B C α β cG cO cT cE f gs (w 4)) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) / D := by
    intro w
    rw [eq_div_iff hD]
    exact ΛS_partsF5B C rfl hd3 α β hα nu E0 cG cO cT cE D f gs hG hperm hcG hcO hcT hcE hkind w
  rw [Finset.sum_filter, sum_words5]
  have hslice : ∀ j : Fin 24, ∑ q ∈ range (24 * slen),
      (if cls5 clsL (Fin.snoc (wordAt q) j) = c then ΛS C α β nu f (Fin.snoc (wordAt q) j) else 0) =
      (-(offAt (tL j.val) c) : ℚ) / D := by
    intro j
    have hS : ∀ P ∈ parts5B C α β cG cO cT cE f gs j, ∀ m, (P.S.rows m).length = 24 := by
      intro P hP m
      simp only [parts5B, List.mem_append, List.mem_map] at hP
      rcases hP with (⟨G, _, rfl⟩ | hP) | hP
      · exact sliceSpec_rows_length _ _ _ _ _ _ _
      · split_ifs at hP with hf
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
          rcases hP with rfl | rfl <;> exact rank1Spec_rows _ _ m
        · simp at hP
      · exact eqBoxParts5_rows C f cE j P hP m
    have hF := sliceCheck_sound_key b _ (clsL j.val) (tL j.val) (hchk j) hS c (hkey j)
    have hconv : ∑ q ∈ range (24 * slen),
        (if cls5 clsL (Fin.snoc (wordAt q) j) = c then ΛS C α β nu f (Fin.snoc (wordAt q) j) else 0) =
        ((∑ q ∈ range (24 * slen), if (clsL j.val).getD q 0 = c then
          partsF (parts5B C α β cG cO cT cE f gs j) (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2 else 0 : ℤ) : ℚ) / D := by
      push_cast
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq' := Finset.mem_range.1 hq
      have hcl : cls5 clsL (Fin.snoc (wordAt q) j) = (clsL j.val).getD q 0 := by
        unfold cls5
        rw [snoc_w4, Fin.init_snoc, posW_wordAt q hq']
      rw [hcl]
      split_ifs with hc
      · rw [key]
        have hv := wordAt_val q hq'
        rw [snoc_w0, snoc_w1, snoc_w2, snoc_w3, snoc_w4]
        have e0 : (wordAt q 0).val = (wd q).1 := congrArg Prod.fst hv
        have e1 : (wordAt q 1).val = (wd q).2.1 := congrArg (fun x => x.2.1) hv
        have e2 : (wordAt q 2).val = (wd q).2.2.1 := congrArg (fun x => x.2.2.1) hv
        have e3 : (wordAt q 3).val = (wd q).2.2.2 := congrArg (fun x => x.2.2.2) hv
        rw [e0, e1, e2, e3]
      · simp
    rw [hconv, hF]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun j _ => hslice j, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_neg_distrib]
  exact_mod_cast congrArg Neg.neg hoff |>.trans (neg_neg _)

end NPT.K4.Route
