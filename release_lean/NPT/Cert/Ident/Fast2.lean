/-
NPT.Cert.Ident.Fast2 — a faster evaluation layer for the identity check at `n = d ≥ 4` (for the
d = 4..8 identity facts), proved equal to the checked definitions as `NPT.Cert.Ident.Fast` does:
* `jarr`: the compression matrices `J` as nested arrays (`Array.getD` instead of `List.getD` on `n^4` rows);
* `suppG`: the support of an entry rule generated digit by digit (a digit tied by an edge to an earlier digit is
  copied, the others range over `0..n-1`), then filtered by `condF`; it is a permutation of the brute-force `supp`
  (`n^8` pairs), so the support sums agree (`suppG_perm`);
* `mkTabG`: local rows of all modules from supports computed once per rule group at `n = 2` and `n = d`
  (`Fast.mkTab` shares them only for `n = 2, 3`).
-/
import NPT.Cert.Ident.Fast

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-! ### Arrays for `J` -/

/-- `J` as nested arrays. -/
def jarr (J : List (List Int)) : Array (Array Int) := (J.map List.toArray).toArray

lemma jarr_get (J : List (List Int)) (i μ : ℕ) : ((jarr J).getD i #[]).getD μ 0 = (J.getD i []).getD μ 0 := by
  unfold jarr
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases h : J[i]? with
  | none => simp
  | some r => simp

/-! ### Digits -/

/-- The flat index of the four digits `v[o..o+3]` (base `n`, `v[o]` most significant). -/
def fl4 (n : ℕ) (v : List ℕ) (o : ℕ) : ℕ :=
  ((v.getD o 0 * n + v.getD (o + 1) 0) * n + v.getD (o + 2) 0) * n + v.getD (o + 3) 0

lemma dgt_fl4_aux (n a b c e : ℕ) (ha : a < n) (hb : b < n) (hc : c < n) (he : e < n) :
    dgt n 4 (((a * n + b) * n + c) * n + e) 0 = a ∧ dgt n 4 (((a * n + b) * n + c) * n + e) 1 = b ∧
      dgt n 4 (((a * n + b) * n + c) * n + e) 2 = c ∧ dgt n 4 (((a * n + b) * n + c) * n + e) 3 = e := by
  have hn : 0 < n := by omega
  have h1 : (((a * n + b) * n + c) * n + e) / n = (a * n + b) * n + c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt he, zero_add]
  have h2 : ((a * n + b) * n + c) / n = a * n + b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, zero_add]
  have h3 : (a * n + b) / n = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  have p3 : n ^ 3 = n * n * n := by ring
  have p2 : n ^ 2 = n * n := by ring
  simp only [dgt, show 4 - 1 - 0 = 3 from rfl, show 4 - 1 - 1 = 2 from rfl, show 4 - 1 - 2 = 1 from rfl,
    show 4 - 1 - 3 = 0 from rfl, pow_one, pow_zero, Nat.div_one, p3, p2, ← Nat.div_div_eq_div_mul, h1, h2, h3]
  refine ⟨Nat.mod_eq_of_lt ha, ?_, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

lemma fl4_dgt (n x : ℕ) (hx : x < n ^ 4) :
    ((dgt n 4 x 0 * n + dgt n 4 x 1) * n + dgt n 4 x 2) * n + dgt n 4 x 3 = x := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hx
    · exact h
  have p3 : n ^ 3 = n * n * n := by ring
  have p2 : n ^ 2 = n * n := by ring
  have h4 : n ^ 4 = n * n * n * n := by ring
  simp only [dgt, show 4 - 1 - 0 = 3 from rfl, show 4 - 1 - 1 = 2 from rfl, show 4 - 1 - 2 = 1 from rfl,
    show 4 - 1 - 3 = 0 from rfl, pow_one, pow_zero, Nat.div_one, p3, p2]
  have ha : x / (n * n * n) < n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [h4] at hx; linarith
  rw [Nat.mod_eq_of_lt ha]
  have e3 : x / (n * n * n) * n + x / (n * n) % n = x / (n * n) := by
    rw [show n * n * n = n * n * n from rfl, ← Nat.div_div_eq_div_mul x (n * n) n]; exact Nat.div_add_mod' _ _
  have e2 : x / (n * n) * n + x / n % n = x / n := by
    rw [← Nat.div_div_eq_div_mul x n n]; exact Nat.div_add_mod' _ _
  rw [e3, e2]
  exact Nat.div_add_mod' x n

lemma fl4_lt (n : ℕ) (v : List ℕ) (o : ℕ) (h : ∀ i < 4, v.getD (o + i) 0 < n) : fl4 n v o < n ^ 4 := by
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  simp only [Nat.add_zero] at h0
  unfold fl4
  have e4 : n ^ 4 = n * n * n * n := by ring
  rw [e4]
  have a1 : v.getD o 0 * n + v.getD (o + 1) 0 < n * n := by nlinarith
  have a2 : (v.getD o 0 * n + v.getD (o + 1) 0) * n + v.getD (o + 2) 0 < n * n * n := by nlinarith
  nlinarith

/-! ### Fast supports -/

/-- The four edges `(kpos s, lpos (p⁻¹ s))` (positions `< 8` of the digit string `x ++ y`) of the entry rule at `p`. -/
def edgesR (kpos lpos : List ℕ) (p : Fin 24) : List (ℕ × ℕ) :=
  (List.finRange 4).map fun s => ((kpos.getD s.val 0) % 8, (lpos.getD (pinvf p s).val 0) % 8)

/-- An earlier position tied to position `c` by an edge (the first one found). -/
def earlier (E : List (ℕ × ℕ)) (c : ℕ) : Option ℕ :=
  E.findSome? fun e => if e.1 = c ∧ e.2 < c then some e.2 else if e.2 = c ∧ e.1 < c then some e.1 else none

lemma earlier_spec {E : List (ℕ × ℕ)} {c c' : ℕ} (h : earlier E c = some c') :
    c' < c ∧ ((c, c') ∈ E ∨ (c', c) ∈ E) := by
  unfold earlier at h
  obtain ⟨e, he, hfe⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨a, b⟩ := e
  dsimp only at hfe
  split_ifs at hfe with h1 h2
  · cases hfe; obtain ⟨rfl, hb⟩ := h1; exact ⟨hb, Or.inl he⟩
  · cases hfe; obtain ⟨rfl, ha⟩ := h2; exact ⟨ha, Or.inr he⟩

/-- Digit strings of length `c` (position `0` first) in which a digit tied to an earlier one copies it. -/
def candL (n : ℕ) (E : List (ℕ × ℕ)) : ℕ → List (List ℕ)
  | 0 => [[]]
  | c + 1 => (candL n E c).flatMap fun pre =>
      match earlier E c with
      | some c' => [pre ++ [pre.getD c' 0]]
      | none => (List.range n).map fun d => pre ++ [d]

/-- The digit strings produced by `candL`. -/
def Good (n : ℕ) (E : List (ℕ × ℕ)) (c : ℕ) (v : List ℕ) : Prop :=
  v.length = c ∧ (∀ i < c, v.getD i 0 < n) ∧ (∀ i < c, ∀ c', earlier E i = some c' → v.getD i 0 = v.getD c' 0)

lemma getD_append_lt (pre : List ℕ) (x i : ℕ) (hi : i < pre.length) : (pre ++ [x]).getD i 0 = pre.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_eq (pre : List ℕ) (x : ℕ) : (pre ++ [x]).getD pre.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

lemma mem_candL (n : ℕ) (E : List (ℕ × ℕ)) (c : ℕ) (v : List ℕ) : v ∈ candL n E c ↔ Good n E c v := by
  induction c generalizing v with
  | zero =>
    simp only [candL, List.mem_singleton, Good]
    constructor
    · rintro rfl; exact ⟨rfl, fun i h => absurd h (Nat.not_lt_zero _), fun i h => absurd h (Nat.not_lt_zero _)⟩
    · rintro ⟨h, -, -⟩; exact List.eq_nil_of_length_eq_zero h
  | succ c ih =>
    simp only [candL, List.mem_flatMap]
    constructor
    · rintro ⟨pre, hpre, hv⟩
      obtain ⟨hl, hd, hf⟩ := (ih pre).1 hpre
      have key : ∀ x, x < n → (∀ c', earlier E c = some c' → x = pre.getD c' 0) → Good n E (c + 1) (pre ++ [x]) := by
        intro x hx hxf
        refine ⟨by simp [hl], fun i hi => ?_, fun i hi c' hc' => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [getD_append_lt _ _ _ (hl ▸ hi)]; exact hd i hi
          · rw [← hl, getD_append_eq]; exact hx
        · have hc'i := (earlier_spec hc').1
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · rw [getD_append_lt _ _ _ (hl ▸ hi), getD_append_lt _ _ _ (hl ▸ (hc'i.trans hi))]; exact hf i hi c' hc'
          · rw [← hl, getD_append_eq, getD_append_lt _ _ _ (hl ▸ hc'i)]; exact hxf c' (hl ▸ hc')
      split at hv
      · next c' hc =>
        rw [List.mem_singleton] at hv; subst hv
        refine key _ ?_ ?_
        · exact hd c' (earlier_spec hc).1
        · intro c'' hc''; rw [hc] at hc''; cases hc''; rfl
      · next hc =>
        rw [List.mem_map] at hv
        obtain ⟨x, hx, rfl⟩ := hv
        exact key x (List.mem_range.1 hx) (fun c' hc' => by rw [hc] at hc'; cases hc')
    · rintro ⟨hl, hd, hf⟩
      have hlen : (v.take c).length = c := by simp [hl]
      have hv : v = v.take c ++ [v.getD c 0] := by
        apply List.ext_getElem (by simp [hl])
        intro i h1 h2
        rcases Nat.lt_or_ge i c with hi | hi
        · rw [List.getElem_append_left (by simpa [hlen] using hi)]; simp
        · have hic : i = c := by simp [hl] at h1; omega
          subst hic
          rw [List.getElem_append_right (by simp [hlen])]
          simp [hlen, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
      have htake : ∀ i < c, (v.take c).getD i 0 = v.getD i 0 := by
        intro i hi; simp [List.getD_eq_getElem?_getD, hi]
      refine ⟨v.take c, (ih _).2 ⟨hlen, fun i hi => (htake i hi).symm ▸ hd i (by omega),
        fun i hi c' hc' => ?_⟩, ?_⟩
      · rw [htake i hi, htake c' ((earlier_spec hc').1.trans hi)]; exact hf i (by omega) c' hc'
      · split
        · next c' hc =>
          rw [List.mem_singleton, htake c' (earlier_spec hc).1]
          rw [← hf c (Nat.lt_succ_self c) c' hc]; exact hv
        · next hc =>
          rw [List.mem_map]; exact ⟨v.getD c 0, List.mem_range.2 (hd c (Nat.lt_succ_self c)), hv.symm⟩

lemma candL_nodup (n : ℕ) (E : List (ℕ × ℕ)) (c : ℕ) : (candL n E c).Nodup := by
  induction c with
  | zero => simp [candL]
  | succ c ih =>
    simp only [candL]
    have hext : ∀ pre x, x ∈ (match earlier E c with
        | some c' => [pre ++ [pre.getD c' 0]]
        | none => (List.range n).map fun d => pre ++ [d]) → ∃ y, x = pre ++ [y] := by
      intro pre x hx
      split at hx
      · rw [List.mem_singleton] at hx; exact ⟨_, hx⟩
      · rw [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact ⟨y, rfl⟩
    rw [List.nodup_flatMap]
    refine ⟨fun pre _ => ?_, ?_⟩
    · split
      · exact List.nodup_singleton _
      · exact List.nodup_range.map fun a b h => by simpa using h
    · refine ih.imp_of_mem fun {a b} ha hb hab => ?_
      intro x hxa hxb
      obtain ⟨y, rfl⟩ := hext a x hxa
      obtain ⟨y', hy'⟩ := hext b _ hxb
      have hla := ((mem_candL n E c a).1 ha).1
      have hlb := ((mem_candL n E c b).1 hb).1
      have := congrArg (List.take c) hy'
      rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this
      exact hab this

/-- `(x, y)` (flat indices of the two halves) of an 8-digit string. -/
def toPair (n : ℕ) (v : List ℕ) : ℕ × ℕ := (fl4 n v 0, fl4 n v 4)

lemma toPair_digits (n : ℕ) (E : List (ℕ × ℕ)) (v : List ℕ) (hv : Good n E 8 v) (i : ℕ) (hi : i < 8) :
    v.getD i 0 = if i < 4 then dgt n 4 (toPair n v).1 i else dgt n 4 (toPair n v).2 (i - 4) := by
  obtain ⟨-, hd, -⟩ := hv
  have A := dgt_fl4_aux n (v.getD 0 0) (v.getD 1 0) (v.getD 2 0) (v.getD 3 0) (hd 0 (by norm_num))
    (hd 1 (by norm_num)) (hd 2 (by norm_num)) (hd 3 (by norm_num))
  have B := dgt_fl4_aux n (v.getD 4 0) (v.getD 5 0) (v.getD 6 0) (v.getD 7 0) (hd 4 (by norm_num))
    (hd 5 (by norm_num)) (hd 6 (by norm_num)) (hd 7 (by norm_num))
  simp only [toPair, fl4]
  interval_cases i <;> simp_all

lemma toPair_inj (n : ℕ) (E : List (ℕ × ℕ)) (v w : List ℕ) (hv : Good n E 8 v) (hw : Good n E 8 w)
    (h : toPair n v = toPair n w) : v = w := by
  apply List.ext_getElem (by rw [hv.1, hw.1])
  intro i h1 h2
  have hi : i < 8 := hv.1 ▸ h1
  have e := (toPair_digits n E v hv i hi).trans ((congrArg (fun z => if i < 4 then dgt n 4 z.1 i
    else dgt n 4 z.2 (i - 4)) h).trans (toPair_digits n E w hw i hi).symm)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] using e

/-- The 8 digits of `(x, y)`. -/
def dig8 (n x y : ℕ) : List ℕ :=
  [dgt n 4 x 0, dgt n 4 x 1, dgt n 4 x 2, dgt n 4 x 3, dgt n 4 y 0, dgt n 4 y 1, dgt n 4 y 2, dgt n 4 y 3]

lemma appDig_dig8 (n x y c : ℕ) (hc : c < 8) : appDig n x y c = (dig8 n x y).getD c 0 := by
  interval_cases c <;> simp [appDig, dig8]

lemma condF_edge {n : ℕ} {kpos lpos : List ℕ} {p : Fin 24} {x y : ℕ} (h : condF n kpos lpos p x y = true)
    {a b : ℕ} (he : (a, b) ∈ edgesR kpos lpos p) : appDig n x y a = appDig n x y b ∧ a < 8 ∧ b < 8 := by
  unfold edgesR at he
  rw [List.mem_map] at he
  obtain ⟨s, -, hs⟩ := he
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  unfold condF at h
  rw [List.all_eq_true] at h
  exact ⟨by simpa using h s (List.mem_finRange s), Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

/-- The fast support: candidate digit strings, filtered by the entry-rule condition. -/
def suppG (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) : List (ℕ × ℕ) :=
  ((candL n (edgesR kpos lpos p) 8).map (toPair n)).filter fun xy => condF n kpos lpos p xy.1 xy.2

lemma mem_supp (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) (z : ℕ × ℕ) :
    z ∈ supp n kpos lpos p ↔ z.1 < n ^ 4 ∧ z.2 < n ^ 4 ∧ condF n kpos lpos p z.1 z.2 = true := by
  obtain ⟨x, y⟩ := z
  simp only [supp, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨x', hx', y', ⟨hy', hc⟩, rfl, rfl⟩; exact ⟨hx', hy', hc⟩
  · rintro ⟨hx, hy, hc⟩; exact ⟨x, hx, y, ⟨hy, hc⟩, rfl, rfl⟩

lemma supp_nodup (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) : (supp n kpos lpos p).Nodup := by
  unfold supp
  rw [List.nodup_flatMap]
  refine ⟨fun x _ => (List.nodup_range.filter _).map fun a b h => by simpa using h, ?_⟩
  refine List.nodup_range.imp_of_mem fun {a b} _ _ hab => ?_
  intro z hza hzb
  rw [List.mem_map] at hza hzb
  obtain ⟨y, -, rfl⟩ := hza
  obtain ⟨y', -, hy'⟩ := hzb
  exact hab (congrArg Prod.fst hy').symm

lemma mem_suppG (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) (z : ℕ × ℕ) :
    z ∈ suppG n kpos lpos p ↔ z.1 < n ^ 4 ∧ z.2 < n ^ 4 ∧ condF n kpos lpos p z.1 z.2 = true := by
  unfold suppG
  rw [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hc⟩
    obtain ⟨-, hd, -⟩ := (mem_candL _ _ _ v).1 hv
    refine ⟨fl4_lt n v 0 fun i hi => hd _ (by omega), fl4_lt n v 4 fun i hi => hd _ (by omega), hc⟩
  · rintro ⟨hx, hy, hc⟩
    obtain ⟨x, y⟩ := z
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hx
      · exact h
    refine ⟨⟨dig8 n x y, (mem_candL _ _ _ _).2 ⟨by simp [dig8], fun i hi => ?_, fun i hi c' hc' => ?_⟩, ?_⟩, hc⟩
    · rw [← appDig_dig8 n x y i hi]
      unfold appDig dgt
      split_ifs <;> exact Nat.mod_lt _ hn
    · obtain ⟨hlt, hmem⟩ := earlier_spec hc'
      rw [← appDig_dig8 n x y i hi, ← appDig_dig8 n x y c' (by omega)]
      rcases hmem with hm | hm
      · exact (condF_edge hc hm).1
      · exact (condF_edge hc hm).1.symm
    · simp only [toPair, fl4, dig8]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [fl4_dgt n x hx, fl4_dgt n y hy]

lemma suppG_nodup (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) : (suppG n kpos lpos p).Nodup := by
  unfold suppG
  refine List.Nodup.filter _ ((candL_nodup n _ 8).map_on fun v hv w hw h => ?_)
  exact toPair_inj n _ v w ((mem_candL _ _ _ _).1 hv) ((mem_candL _ _ _ _).1 hw) h

/-- **The fast support is a permutation of the brute-force support.** -/
theorem suppG_perm (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) : (suppG n kpos lpos p).Perm (supp n kpos lpos p) := by
  rw [List.perm_ext_iff_of_nodup (suppG_nodup n kpos lpos p) (supp_nodup n kpos lpos p)]
  intro z
  rw [mem_suppG, mem_supp]

/-! ### Local rows from fast supports -/

/-- Fast supports of all `24` permutations. -/
def suppsG (n : ℕ) (kpos lpos : List ℕ) : List (List (ℕ × ℕ)) := (List.finRange 24).map (suppG n kpos lpos)

/-- Local rows from supports, `J` as arrays. -/
def localRowsA (md : ModD) (JA : Array (Array Int)) (S : List (List (ℕ × ℕ))) : List (List SInt) :=
  (List.finRange 24).map fun p => (List.range (md.dim * md.dim)).map fun k =>
    SInt.ofInt (((S.getD p.val []).map fun xy =>
      (JA.getD xy.1 #[]).getD (k / md.dim) 0 * (JA.getD xy.2 #[]).getD (k % md.dim) 0).sum)

lemma localRowsA_eq (md : ModD) (kpos lpos : List ℕ) :
    localRowsA md (jarr md.J) (suppsG md.n kpos lpos) = localRowsF md kpos lpos := by
  rw [← localRowsS_eq md kpos lpos]
  unfold localRowsA localRowsS
  refine List.map_congr_left fun p _ => List.map_congr_left fun k _ => ?_
  congr 1
  rw [suppsG, supps, map_finRange_getD, map_finRange_getD]
  simp only [jarr_get]
  exact ((suppG_perm _ _ _ p).map _).sum_eq

/-- Local rows of all modules for one entry rule, with the supports at `n = 2` and `n = d` computed once. -/
def mkTabG (C : CertD) (kpos lpos : List ℕ) (s2 sd : List (List (ℕ × ℕ))) : List (List (List SInt)) :=
  C.mods.map fun md => localRowsA md (jarr md.J)
    (if md.n = 2 then s2 else if md.n = C.d then sd else suppsG md.n kpos lpos)

lemma mkTabG_eq (C : CertD) (kpos lpos : List ℕ) :
    mkTabG C kpos lpos (suppsG 2 kpos lpos) (suppsG C.d kpos lpos) = C.mods.map fun md => localRowsF md kpos lpos := by
  unfold mkTabG
  refine List.map_congr_left fun md _ => ?_
  split_ifs with h2 hd
  · rw [← h2, localRowsA_eq]
  · rw [← hd, localRowsA_eq]
  · rw [localRowsA_eq]

lemma ruleSpecT_G (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) :
    ruleSpecT C zmul coef kpos lpos (mkTabG C kpos lpos (suppsG 2 kpos lpos) (suppsG C.d kpos lpos)) =
      ruleSpecF C zmul coef kpos lpos := by
  unfold ruleSpecT ruleSpecF
  congr 1
  funext m
  rw [mkTabG_eq, getD_map']

/-- The parts of family `f`, rule groups with tabulated local rows from fast supports. -/
def famPartsG (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  gs.map (fun G => ⟨ruleSpecT C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos
      (mkTabG C G.kpos G.lpos (suppsG 2 G.kpos G.lpos) (suppsG C.d G.kpos G.lpos)), G.tree⟩) ++
    (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []) ++ eqPartsF C f eqT

lemma famPartsG_eq (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : famPartsG C zmul f gs zs za eqT = famParts C zmul f gs zs za eqT := by
  unfold famPartsG famParts
  congr 2
  refine List.map_congr_left fun G _ => ?_
  rw [ruleSpecT_G]

/-! ### Equality local maps: a table per spec -/

/-- The pairs `(a, b)` of `J` rows in `delFast`'s sum (`k < n^4` with the traced-digit condition). -/
def delPairs (slot : ℕ) (order : List ℕ) (n : ℕ) [NeZero n] (p : Fin 24) : List (ℕ × ℕ) :=
  ((List.range (n ^ 4)).filter fun k => decide (unflat n 4 k (sF slot) = unflat n 4 k (pf p (sF slot)))).map fun k =>
    (flat (unflat n 4 k ∘ oF order), flat (unflat n 4 k ∘ pf p ∘ oF order))

lemma list_sum_ite_filter (L : List ℕ) (c : ℕ → Prop) [DecidablePred c] (h : ℕ → ℤ) :
    (L.map fun k => if c k then h k else 0).sum = ((L.filter fun k => decide (c k)).map h).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases hc : c a <;> simp [hc, ih]

lemma delFast_pairs (J : List (List Int)) (slot : ℕ) (order : List ℕ) (n : ℕ) [NeZero n] (p : Fin 24) (μ ν : ℕ) :
    delFast J slot order n p μ ν =
      ((delPairs slot order n p).map fun ab => (J.getD ab.1 []).getD μ 0 * (J.getD ab.2 []).getD ν 0).sum := by
  unfold delFast delPairs
  rw [finset_sum_range_listZ, List.map_map, list_sum_ite_filter]
  rfl

/-- `delPairs` for any `n` (empty for `n = 0`). -/
def delPairsN (slot : ℕ) (order : List ℕ) (n : ℕ) (p : Fin 24) : List (ℕ × ℕ) :=
  if hn : n = 0 then [] else haveI : NeZero n := ⟨hn⟩; delPairs slot order n p

/-- `eqLocF` with the `del` pairs `prs` precomputed and the `J` of every module as arrays (`JA`). -/
def eqLocP (C : CertD) (JA : List (Array (Array Int))) (sp : EqSpecD) (n : ℕ) (p : Fin 24)
    (prs : List (ℕ × ℕ)) (o : ℕ) : ℤ :=
  let dec := C.eqDecode sp.mkeys o
  let mi := sp.mkeys.getD dec.1 0
  let md := C.mods.getD mi default
  if dec.2.1 < md.dim then if dec.2.2 < md.dim then
    if sp.kind = 0 then
      if hn : n = 0 then 0 else
        haveI : NeZero n := ⟨hn⟩
        if SOk sp.slot sp.order then
          (let A := JA.getD mi #[]
           (prs.map fun ab => (A.getD ab.1 #[]).getD dec.2.1 0 * (A.getD ab.2 #[]).getD dec.2.2 0).sum)
        else delB md.J sp.slot sp.order n p dec.2.1 dec.2.2
    else stiefF md.J sp.slot p dec.2.1 dec.2.2
  else 0 else 0

/-- The arrays of all modules. -/
def jarrs (C : CertD) : List (Array (Array Int)) := C.mods.map fun md => jarr md.J

lemma jarrs_getD (C : CertD) (mi : ℕ) (a μ : ℕ) :
    (((jarrs C).getD mi #[]).getD a #[]).getD μ 0 = ((C.mods.getD mi default).J.getD a []).getD μ 0 := by
  unfold jarrs
  rw [show (#[] : Array (Array Int)) = jarr (default : ModD).J from rfl, getD_map', jarr_get]

lemma eqLocP_eq (C : CertD) (sp : EqSpecD) (n : ℕ) (p : Fin 24) (o : ℕ) :
    eqLocP C (jarrs C) sp n p (delPairsN sp.slot sp.order n p) o = eqLocF C sp n p o := by
  unfold eqLocP eqLocF
  dsimp only
  split_ifs with hμ hν hk hn hso
  · rfl
  · rw [delFast_pairs]
    simp only [delPairsN, hn, ↓reduceDIte, jarrs_getD]
  · rfl
  · rfl
  · rfl
  · rfl

/-- Table of `eqLocP` for `p < 24`, `o < nO` (one spec, one leg dimension `n`). -/
def eqRowT (C : CertD) (JA : List (Array (Array Int))) (sp : EqSpecD) (n nO : ℕ) : Array (Array Int) :=
  ((List.finRange 24).map fun p =>
    let prs := delPairsN sp.slot sp.order n p
    ((List.range nO).map fun o => eqLocP C JA sp n p prs o).toArray).toArray

/-- Equality of specs as a `Bool`. -/
def specBEq (a b : EqSpecD) : Bool := a.slot == b.slot && a.order == b.order && a.kind == b.kind && a.mkeys == b.mkeys

lemma specBEq_eq {a b : EqSpecD} (h : specBEq a b = true) : a = b := by
  obtain ⟨s1, o1, k1, m1⟩ := a
  obtain ⟨s2, o2, k2, m2⟩ := b
  simp only [specBEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

/-- Range of `o` for a spec: the stacked rows of its modules. -/
def nOf (C : CertD) (sp : EqSpecD) : ℕ := (sp.mkeys.map fun m => mdim C m * mdim C m).sum

/-- The `(spec, leg dimension)` keys of family `f`'s equality parts. -/
def eqKeys (C : CertD) (f : ℕ) : List (EqSpecD × ℕ) :=
  C.eqs.flatMap fun g => g.parts.flatMap fun P => if P.fam = f then
    (List.range 4).map fun l => (P.specs.getD l default, nfN C.d l) else []

/-- The table of family `f`: for each key, the `eqLocP` table. -/
def eqTab (C : CertD) (JA : List (Array (Array Int))) (f : ℕ) : List (EqSpecD × ℕ × Array (Array Int)) :=
  (eqKeys C f).map fun k => (k.1, k.2, eqRowT C JA k.1 k.2 (nOf C k.1))

/-- Look up `(sp, n, p, o)` in the table (fallback `eqLocF`). -/
def eqLook (C : CertD) (tab : List (EqSpecD × ℕ × Array (Array Int))) (sp : EqSpecD) (n : ℕ) (p : Fin 24)
    (o : ℕ) : ℤ :=
  match tab.find? (fun e => specBEq e.1 sp && e.2.1 == n) with
  | some e => if o < (e.2.2.getD p.val #[]).size then (e.2.2.getD p.val #[]).getD o 0 else eqLocF C sp n p o
  | none => eqLocF C sp n p o

lemma toArray_getD {α : Type*} (L : List α) (i : ℕ) (d : α) : L.toArray.getD i d = L.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

lemma eqRowT_get (C : CertD) (sp : EqSpecD) (n nO : ℕ) (p : Fin 24) (o : ℕ)
    (ho : o < ((eqRowT C (jarrs C) sp n nO).getD p.val #[]).size) :
    ((eqRowT C (jarrs C) sp n nO).getD p.val #[]).getD o 0 = eqLocF C sp n p o := by
  have hrow : (eqRowT C (jarrs C) sp n nO).getD p.val #[] =
      ((List.range nO).map fun o => eqLocP C (jarrs C) sp n p (delPairsN sp.slot sp.order n p) o).toArray := by
    unfold eqRowT
    rw [toArray_getD, show (#[] : Array Int) = (List.map (fun o => eqLocP C (jarrs C) sp n p
      (delPairsN sp.slot sp.order n p) o) (List.range 0)).toArray from rfl]
    exact map_finRange_getD (fun p => ((List.range nO).map fun o => eqLocP C (jarrs C) sp n p
      (delPairsN sp.slot sp.order n p) o).toArray) _ p |>.trans (by rfl)
  rw [hrow] at ho ⊢
  simp only [List.size_toArray, List.length_map, List.length_range] at ho
  rw [toArray_getD, getD_range_map _ _ _ _ ho]
  exact eqLocP_eq C sp n p o

lemma eqLook_eq (C : CertD) (f : ℕ) : eqLook C (eqTab C (jarrs C) f) = eqLocF C := by
  funext sp n p o
  unfold eqLook
  split
  · next e he =>
    have hmem := List.mem_of_find?_eq_some he
    have hpe := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hpe
    obtain ⟨hs, hn⟩ := hpe
    have hs := specBEq_eq hs
    unfold eqTab at hmem
    rw [List.mem_map] at hmem
    obtain ⟨k, -, rfl⟩ := hmem
    dsimp only at hs hn ⊢
    subst hs hn
    by_cases ho : o < ((eqRowT C (jarrs C) k.1 k.2 (nOf C k.1)).getD p.val #[]).size
    · rw [ite_eq_left ho]; exact eqRowT_get C k.1 k.2 _ p o ho
    · rw [ite_eq_right ho]
  · rfl

/-- The parts of family `f` with fast rule-group rows and the equality table. -/
def famPartsG2 (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) : List Part :=
  famPartsG C zmul f gs zs za (eqLook C (eqTab C (jarrs C) f))

lemma famPartsG2_eq (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) :
    famPartsG2 C zmul f gs zs za = famParts C zmul f gs zs za (eqLocF C) := by
  unfold famPartsG2
  rw [eqLook_eq, famPartsG_eq]

end NPT.Cert.Ident
