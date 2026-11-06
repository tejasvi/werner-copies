/-
NPT.Restrict — the endpoint property passes from all copies to any subset of them:
for `t < 1`, `EP ι d t → EP (In S) d t`, via the extension `X ↦ X ⊗ |0⟩⟨0|^{⊗ Sᶜ}`.
-/
import NPT.Block

open Matrix BigOperators Finset

namespace NPT

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- `C` is supported on the corner where the indices in `K` vanish. -/
def SuppZero [NeZero d] (K : Finset ι) (C : Op ι d) : Prop :=
  ∀ x y, ¬ (ZeroOn K x ∧ ZeroOn K y) → C x y = 0

/-- Extension of a function on `J \ K` by zero on `J ∩ K`. -/
def extZero [NeZero d] (J K : Finset ι) (w : (J \ K : Finset ι) → Fin d) : J → Fin d :=
  fun j => if h : j.1 ∈ K then 0 else w ⟨j.1, Finset.mem_sdiff.mpr ⟨j.2, h⟩⟩

lemma extZero_injective [NeZero d] (J K : Finset ι) : Function.Injective (extZero (d := d) J K) := by
  intro w w' h
  funext i
  have hiJ : i.1 ∈ J := (Finset.mem_sdiff.mp i.2).1
  have hiK : i.1 ∉ K := (Finset.mem_sdiff.mp i.2).2
  have := congrFun h ⟨i.1, hiJ⟩
  simpa [extZero, hiK] using this

/-- A sum over `z : J → Fin d` of terms vanishing unless `z = 0` on `J ∩ K` reduces to `J \ K`. -/
lemma sum_eq_sum_extZero [NeZero d] {M : Type*} [AddCommMonoid M] (J K : Finset ι) (F : (J → Fin d) → M)
    (hF : ∀ z : J → Fin d, (∃ j : J, j.1 ∈ K ∧ z j ≠ 0) → F z = 0) :
    ∑ z, F z = ∑ w, F (extZero J K w) := by
  have hs : (Finset.univ.map ⟨extZero (d := d) J K, extZero_injective J K⟩) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hs, Finset.sum_map]
  · rfl
  · intro z _ hz
    apply hF
    by_contra hcon
    push Not at hcon
    apply hz
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    refine ⟨fun i => z ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩, ?_⟩
    funext j
    by_cases hjK : j.1 ∈ K
    · simp [extZero, hjK, hcon j hjK]
    · simp [extZero, hjK]

/-- Tracing over copies on which `C` is supported at `0` does nothing. -/
lemma ptrace_sdiff_of_supp [NeZero d] {K : Finset ι} {C : Op ι d} (hC : SuppZero K C) (J : Finset ι) :
    ptrace J C = ptrace (J \ K) C := by
  funext x y
  by_cases hJ : ZeroOn J x ∧ ZeroOn J y
  · have hJK : ZeroOn (J \ K) x ∧ ZeroOn (J \ K) y :=
      ⟨fun i hi => hJ.1 i (Finset.mem_sdiff.mp hi).1, fun i hi => hJ.2 i (Finset.mem_sdiff.mp hi).1⟩
    rw [ptrace_apply_pos hJ, ptrace_apply_pos hJK]
    rw [sum_eq_sum_extZero J K]
    · refine Finset.sum_congr rfl fun w _ => ?_
      have hu : ∀ v : Idx ι d, ZeroOn J v → upd J v (extZero J K w) = upd (J \ K) v w := by
        intro v hv
        funext i
        by_cases hiJ : i ∈ J
        · by_cases hiK : i ∈ K
          · have : i ∉ J \ K := by simp [hiK]
            simp [upd, extZero, hiJ, hiK, this, hv i hiJ]
          · have : i ∈ J \ K := by simp [hiJ, hiK]
            simp [upd, extZero, hiJ, hiK, this]
        · have : i ∉ J \ K := by simp [hiJ]
          simp [upd, hiJ, this]
      rw [hu x hJ.1, hu y hJ.2]
    · rintro z ⟨j, hjK, hj⟩
      apply hC
      intro h
      apply hj
      have := h.1 j.1 hjK
      simpa [upd, j.2] using this
  · rw [ptrace_apply_neg hJ]
    by_cases hJK : ZeroOn (J \ K) x ∧ ZeroOn (J \ K) y
    · rw [ptrace_apply_pos hJK]
      symm
      refine Finset.sum_eq_zero fun w _ => ?_
      apply hC
      intro h
      apply hJ
      constructor
      · intro i hiJ
        by_cases hiK : i ∈ K
        · have hnot : i ∉ J \ K := by simp [hiK]
          have := h.1 i hiK
          simpa [upd, hnot] using this
        · exact hJK.1 i (by simp [hiJ, hiK])
      · intro i hiJ
        by_cases hiK : i ∈ K
        · have hnot : i ∉ J \ K := by simp [hiK]
          have := h.2 i hiK
          simpa [upd, hnot] using this
        · exact hJK.2 i (by simp [hiJ, hiK])
    · rw [ptrace_apply_neg hJK]

/-- Extension `X ⊗ |0⟩⟨0|^{⊗ Sᶜ}` of an operator on the copies in `S`. -/
def ext [NeZero d] (S : Finset ι) (X : Op (In S) d) : Op ι d := fun x y =>
  if ZeroOn Sᶜ x ∧ ZeroOn Sᶜ y then X (fun i => x i.1) (fun i => y i.1) else 0

lemma ext_apply_pos [NeZero d] {S : Finset ι} {X : Op (In S) d} {x y : Idx ι d}
    (h : ZeroOn Sᶜ x ∧ ZeroOn Sᶜ y) : ext S X x y = X (fun i => x i.1) (fun i => y i.1) := by
  show (if ZeroOn Sᶜ x ∧ ZeroOn Sᶜ y then _ else _) = _
  rw [if_pos h]

lemma ext_apply_neg [NeZero d] {S : Finset ι} {X : Op (In S) d} {x y : Idx ι d}
    (h : ¬ (ZeroOn Sᶜ x ∧ ZeroOn Sᶜ y)) : ext S X x y = 0 := by
  show (if ZeroOn Sᶜ x ∧ ZeroOn Sᶜ y then _ else _) = _
  rw [if_neg h]

lemma suppZero_ext [NeZero d] (S : Finset ι) (X : Op (In S) d) : SuppZero Sᶜ (ext S X) :=
  fun _ _ h => ext_apply_neg h

theorem rank_ext [NeZero d] (S : Finset ι) {X : Op (In S) d} (hX : RankLE2 X) : RankLE2 (ext S X) := by
  obtain ⟨A, B, rfl⟩ := hX
  refine ⟨Matrix.of fun x r => if ZeroOn Sᶜ x then A (fun i => x i.1) r else 0,
          Matrix.of fun y r => if ZeroOn Sᶜ y then B (fun i => y i.1) r else 0, ?_⟩
  ext x y
  rw [Matrix.mul_apply]
  by_cases hx : ZeroOn Sᶜ x <;> by_cases hy : ZeroOn Sᶜ y
  · rw [ext_apply_pos ⟨hx, hy⟩, Matrix.mul_apply]; simp [hx, hy]
  · rw [ext_apply_neg (fun h => hy h.2)]; simp [hy]
  · rw [ext_apply_neg (fun h => hx h.1)]; simp [hx]
  · rw [ext_apply_neg (fun h => hx h.1)]; simp [hx]

lemma zeroOn_compl_glue [NeZero d] (S : Finset ι) (u : Idx (In S) d) (a : Idx (Out S) d) :
    ZeroOn Sᶜ (glue S u a) ↔ a = 0 := by
  constructor
  · intro h
    funext i
    have := h i.1 (by simpa using i.2)
    simpa [glue, i.2] using this
  · rintro rfl i hi
    have hiS : i ∉ S := by simpa using hi
    simp [glue, hiS]

lemma block_ext [NeZero d] (S : Finset ι) (X : Op (In S) d) (a b : Idx (Out S) d) :
    block S a b (ext S X) = if a = 0 ∧ b = 0 then X else 0 := by
  funext u v
  simp only [block]
  by_cases hab : a = 0 ∧ b = 0
  · have h : ZeroOn Sᶜ (glue S u a) ∧ ZeroOn Sᶜ (glue S v b) :=
      ⟨(zeroOn_compl_glue S u a).2 hab.1, (zeroOn_compl_glue S v b).2 hab.2⟩
    rw [ext_apply_pos h, if_pos hab]
    congr 1 <;> funext i <;> simp [glue, i.2]
  · have h : ¬ (ZeroOn Sᶜ (glue S u a) ∧ ZeroOn Sᶜ (glue S v b)) := by
      rwa [zeroOn_compl_glue, zeroOn_compl_glue]
    rw [ext_apply_neg h, if_neg hab]
    rfl

lemma ptrace_zero [NeZero d] (J : Finset ι) : ptrace J (0 : Op ι d) = 0 := by
  funext x y
  by_cases h : ZeroOn J x ∧ ZeroOn J y
  · rw [ptrace_apply_pos h]; simp
  · rw [ptrace_apply_neg h]; rfl

lemma frobSq_zero : frobSq (0 : Op ι d) = 0 := by simp [frobSq]

/-- Norms of partial traces of an extension. -/
lemma frobSq_ptrace_ext [NeZero d] (S : Finset ι) (X : Op (In S) d) (J : Finset ι) :
    frobSq (ptrace J (ext S X)) = frobSq (ptrace (toIn S (J ∩ S)) X) := by
  have hJS : J \ Sᶜ = J ∩ S := by ext i; simp
  rw [ptrace_sdiff_of_supp (suppZero_ext S X) J, hJS]
  rw [frobSq_ptrace_eq_sum_block (Finset.inter_subset_right)]
  simp_rw [block_ext]
  have : ∀ a b : Idx (Out S) d, frobSq (ptrace (toIn S (J ∩ S)) (if a = 0 ∧ b = 0 then X else 0))
      = if a = 0 then (if b = 0 then frobSq (ptrace (toIn S (J ∩ S)) X) else 0) else 0 := by
    intro a b
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, ptrace_zero, frobSq_zero]
  simp_rw [this]
  simp

/-- Reindexing subsets of `S` as subsets of `In S`. -/
lemma sum_powerset_toIn {M : Type*} [AddCommMonoid M] (S : Finset ι) (G : Finset (In S) → M) :
    ∑ J ∈ S.powerset, G (toIn S J) = ∑ J' : Finset (In S), G J' := by
  refine Finset.sum_nbij' (fun J => toIn S J) (fun J' => J'.map ⟨Subtype.val, Subtype.val_injective⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro J _; exact Finset.mem_univ _
  · intro J' _
    simp only [Finset.mem_powerset]
    intro x hx
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  · intro J hJ
    have hJS := Finset.mem_powerset.mp hJ
    ext x
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, toIn, Finset.mem_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hJS hx⟩, hx, rfl⟩
  · intro J' _
    ext x
    simp [toIn, Finset.mem_subtype]
  · intro J _; rfl

/-- Splitting subsets of `ι` into their parts in `S` and in `Sᶜ`. -/
lemma sum_finset_split {M : Type*} [AddCommMonoid M] (S : Finset ι) (f : Finset ι → M) :
    ∑ J : Finset ι, f J = ∑ J1 ∈ S.powerset, ∑ J2 ∈ Sᶜ.powerset, f (J1 ∪ J2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun J => (J ∩ S, J ∩ Sᶜ)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro J _
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro _ _; exact Finset.mem_univ _
  · intro J _
    ext i; by_cases hi : i ∈ S <;> simp [hi]
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_powerset] at hp
    obtain ⟨h1, h2⟩ := hp
    ext i
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hS⟩
        · exact h
        · exact absurd hS (by simpa using h2 h)
      · intro h; exact ⟨Or.inl h, h1 h⟩
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hS⟩
        · exact absurd (h1 h) (by simpa using hS)
        · exact h
      · intro h; exact ⟨Or.inr h, h2 h⟩
  · intro J _
    simp only
    congr 1
    ext i; by_cases hi : i ∈ S <;> simp [hi]

/-- `q` of an extension: `q_ι(t, X ⊗ |0⟩⟨0|^{⊗Sᶜ}) = (1-t)^{|Sᶜ|} q_S(t, X)`. -/
theorem q_ext [NeZero d] (S : Finset ι) (X : Op (In S) d) (t : ℝ) :
    q t (ext S X) = (1 - t) ^ Sᶜ.card * q t X := by
  unfold q
  simp_rw [frobSq_ptrace_ext]
  rw [sum_finset_split S]
  have h1 : ∀ J1 ∈ S.powerset, ∀ J2 ∈ Sᶜ.powerset,
      (-t) ^ (J1 ∪ J2).card * frobSq (ptrace (toIn S ((J1 ∪ J2) ∩ S)) X)
        = ((-t) ^ J2.card) * ((-t) ^ (toIn S J1).card * frobSq (ptrace (toIn S J1) X)) := by
    intro J1 hJ1 J2 hJ2
    have hJ1S := Finset.mem_powerset.mp hJ1
    have hJ2S := Finset.mem_powerset.mp hJ2
    have hdisj : Disjoint J1 J2 := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have := hJ2S hi2
      simp [hJ1S hi1] at this
    have hint : (J1 ∪ J2) ∩ S = J1 := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hS⟩
        · exact h
        · exact absurd hS (by simpa using hJ2S h)
      · intro h; exact ⟨Or.inl h, hJ1S h⟩
    rw [hint, Finset.card_union_of_disjoint hdisj, card_toIn hJ1S, pow_add]
    ring
  rw [Finset.sum_congr rfl fun J1 hJ1 => Finset.sum_congr rfl fun J2 hJ2 => h1 J1 hJ1 J2 hJ2]
  simp_rw [← Finset.sum_mul]
  have h2 : ∑ J2 ∈ Sᶜ.powerset, (-t) ^ J2.card = (1 - t) ^ Sᶜ.card := by
    have := Finset.sum_pow_mul_eq_add_pow (-t) (1 : ℝ) Sᶜ
    simp only [one_pow, mul_one] at this
    rw [this]; ring_nf
  simp_rw [h2, ← Finset.mul_sum]
  congr 1
  exact sum_powerset_toIn S (fun J' => (-t) ^ J'.card * frobSq (ptrace J' X))

/-- The endpoint property passes to any subset of the copies (for `t < 1`). -/
theorem EP_restrict [NeZero d] (S : Finset ι) {t : ℝ} (ht : t < 1) (h : EP ι d t) : EP (In S) d t := by
  intro X hX
  have := h (ext S X) (rank_ext S hX)
  rw [q_ext] at this
  exact (mul_nonneg_iff_of_pos_left (pow_pos (by linarith) _)).mp this

/-- Monotonicity in `t`: `EP ι d g` implies `EP ι d t` for all `0 ≤ t ≤ g < 1`. -/
theorem EP_mono_t [NeZero d] {g t : ℝ} (hg : 0 < g) (hg1 : g < 1) (ht0 : 0 ≤ t) (htg : t ≤ g)
    (h : EP ι d g) : EP ι d t :=
  EP_of_EP_sub hg ht0 htg fun S => EP_restrict S hg1 h

end NPT
