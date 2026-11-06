/-
NPT.K4.Route.HsumS — the class sums of `ΛS` over all `24^5` words (k = 4, d = 3) from the 24 aux-slice checks and the
offsets: with `cls5 clsL w = (clsL (w 4)).getD (posW (w 0..3)) 0`, every class `c` that is the key of its leaf in all
24 accumulators has `Σ_{w : cls5 w = c} ΛS_f(w) = Rint / D`, where `Σ_j offAt (tL j) c = −Rint`.
-/
import NPT.K4.Route.Assembly5
import NPT.K4.Route.SliceSound

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.K4

/-- The class of a word from the per-slice class lists (slice = aux letter `w 4`, position `posW (w 0, …, w 3)`). -/
def cls5 (clsL : ℕ → List ℕ) (w : Fin (4 + 1) → Fin 24) : ℕ := (clsL (w 4).val).getD (posW (Fin.init w)) 0

/-- Words of `Fin 5 → Fin 24` as (aux letter, site word). -/
def splitEquiv : (Fin (4 + 1) → Fin 24) ≃ Fin 24 × (Fin 4 → Fin 24) where
  toFun w := (w (Fin.last 4), Fin.init w)
  invFun p := Fin.snoc p.2 p.1
  left_inv w := by simp only [Fin.snoc_init_self]
  right_inv p := by simp only [Fin.init_snoc, Fin.snoc_last]

lemma sum_words5 (F : (Fin (4 + 1) → Fin 24) → ℚ) :
    ∑ w, F w = ∑ j : Fin 24, ∑ q ∈ range (24 * slen), F (Fin.snoc (wordAt q) j) := by
  rw [Fintype.sum_equiv splitEquiv F (fun p => F (Fin.snoc p.2 p.1)) (fun w => by
    simp only [splitEquiv, Equiv.coe_fn_mk, Fin.snoc_init_self]), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun q => F (Fin.snoc (wordAt q) j))]
  exact Fintype.sum_equiv posEquiv _ _ fun v => by simp [posEquiv, wordAt_posW]

lemma snoc_w0 (v : Fin 4 → Fin 24) (j : Fin 24) : (Fin.snoc v j : Fin (4 + 1) → Fin 24) 0 = v 0 := rfl
lemma snoc_w1 (v : Fin 4 → Fin 24) (j : Fin 24) : (Fin.snoc v j : Fin (4 + 1) → Fin 24) 1 = v 1 := rfl
lemma snoc_w2 (v : Fin 4 → Fin 24) (j : Fin 24) : (Fin.snoc v j : Fin (4 + 1) → Fin 24) 2 = v 2 := rfl
lemma snoc_w3 (v : Fin 4 → Fin 24) (j : Fin 24) : (Fin.snoc v j : Fin (4 + 1) → Fin 24) 3 = v 3 := rfl
lemma snoc_w4 (v : Fin 4 → Fin 24) (j : Fin 24) : (Fin.snoc v j : Fin (4 + 1) → Fin 24) 4 = j := rfl

/-- **Class sums from the slice checks.** -/
theorem hsum_of_slices (d : ℕ) (types : List TypeD) (mods : List ModD) (eqs : List EqGroupD)
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
    (hchk : ∀ j : Fin 24, sliceCheck b (parts5 ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ α β cG cO cT cE f gs j)
      (clsL j.val) (tL j.val) = true)
    (c : ℕ) (hkey : ∀ j : Fin 24, ((tL j.val).leaves.getD ((tL j.val).tgt c) dLeaf).1 = c)
    (Rint : ℤ) (hoff : ∑ j : Fin 24, offAt (tL j.val) c = -Rint) :
    ∑ w ∈ univ.filter (fun w : Fin (4 + 1) → Fin 24 => cls5 clsL w = c),
      ΛS ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ α β nu f w = (Rint : ℚ) / D := by
  set C : CertD := ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩ with hC
  have key : ∀ w : Fin (4 + 1) → Fin 24, ΛS C α β nu f w =
      ((partsF (parts5 C α β cG cO cT cE f gs (w 4)) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) / D := by
    intro w
    rw [eq_div_iff hD]
    exact ΛS_partsF5 C rfl hd3 α β hα nu E0 cG cO cT cE D f gs hG hperm hcG hcO hcT hcE hkind w
  rw [Finset.sum_filter, sum_words5]
  have hslice : ∀ j : Fin 24, ∑ q ∈ range (24 * slen),
      (if cls5 clsL (Fin.snoc (wordAt q) j) = c then ΛS C α β nu f (Fin.snoc (wordAt q) j) else 0) =
      (-(offAt (tL j.val) c) : ℚ) / D := by
    intro j
    have hS : ∀ P ∈ parts5 C α β cG cO cT cE f gs j, ∀ m, (P.S.rows m).length = 24 := by
      intro P hP m
      simp only [parts5, eqParts5, List.mem_append, List.mem_map, List.mem_flatMap] at hP
      rcases hP with (⟨G, _, rfl⟩ | hP) | hP
      · exact sliceSpec_rows_length _ _ _ _ _ _ _
      · split_ifs at hP with hf
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hP
          rcases hP with rfl | rfl <;> exact rank1Spec_rows _ _ m
        · simp at hP
      · obtain ⟨g, _, P', _, hP'⟩ := hP
        split_ifs at hP' with hf
        · simp only [List.mem_map] at hP'; obtain ⟨ol, _, rfl⟩ := hP'; exact rank1Spec_rows _ _ m
        · simp at hP'
    have hF := sliceCheck_sound_key b _ (clsL j.val) (tL j.val) (hchk j) hS c (hkey j)
    have hconv : ∑ q ∈ range (24 * slen),
        (if cls5 clsL (Fin.snoc (wordAt q) j) = c then ΛS C α β nu f (Fin.snoc (wordAt q) j) else 0) =
        ((∑ q ∈ range (24 * slen), if (clsL j.val).getD q 0 = c then
          partsF (parts5 C α β cG cO cT cE f gs j) (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2 else 0 : ℤ) : ℚ) / D := by
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
