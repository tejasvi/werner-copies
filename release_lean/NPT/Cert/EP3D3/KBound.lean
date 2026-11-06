/-
NPT.Cert.EP3D3.KBound — the crude word-value bounds of `KRBound` / `KRBoundMod` for the d = 3 certificate,
in the forms of the hypotheses `hB`, `hBp`, `hFmod` of `KAssembly.hsumK_f<f>`, stated with `eqLocF cert`
(`= eqTK eqTabsK cert` by `KEqOK.eqTK_eqLocF`):
* `wordBound_f<f>` (`hB`): every word value of family `f` is at most `KB = 2^5487` (`crudeBZ`, with the block scan
  `zqBmax cert zmul ≤ 2^5319` checked once);
* `wordBound_prod` (`hBp`): `24 · slen · KB < ∏ ps3`;
* `wordBoundMod_f<f>` (`hFmod`): for every `p ∈ ps3` (all `≤ 2^600`), every reduced word value is below `2^(bK − 1)`
  (`crudeBMod`, about `2^751`).
-/
import NPT.Cert.EP3D3.IdDefs
import NPT.Cert.EP3D3.KPrimes
import NPT.Cert.Ident.KRBoundMod
set_option maxRecDepth 100000

open NPT.Cert.Ident NPT.Cert.Sem

namespace NPT.Cert.EP3D3

/-- The word-value bound, for every family. -/
def KB : ℕ := 2 ^ 5487

/-- The block scan, checked once. -/
theorem zqBmax_le_K : zqBmax cert zmul ≤ 2 ^ 5319 := by decide +kernel

theorem crudeBZ_le_KB_f0 : crudeBZ cert 0 gs0 zsT zaT (2 ^ 5319) ≤ KB := by decide +kernel
theorem crudeBZ_le_KB_f1 : crudeBZ cert 1 gs1 zsT zaT (2 ^ 5319) ≤ KB := by decide +kernel
theorem crudeBZ_le_KB_f2 : crudeBZ cert 2 gs2 zsT zaT (2 ^ 5319) ≤ KB := by decide +kernel

theorem wordBound_f0 : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famParts cert zmul 0 gs0 zsT zaT (eqLocF cert)) w0 w1 w2 w3| ≤ KB := fun w0 w1 w2 w3 h0 h1 h2 h3 =>
  le_trans (partsF_le_crudeBZ_eqLocF cert zmul 0 gs0 zsT zaT _ zqBmax_le_K w0 w1 w2 w3 h0 h1 h2 h3)
    (by exact_mod_cast crudeBZ_le_KB_f0)

theorem wordBound_f1 : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famParts cert zmul 1 gs1 zsT zaT (eqLocF cert)) w0 w1 w2 w3| ≤ KB := fun w0 w1 w2 w3 h0 h1 h2 h3 =>
  le_trans (partsF_le_crudeBZ_eqLocF cert zmul 1 gs1 zsT zaT _ zqBmax_le_K w0 w1 w2 w3 h0 h1 h2 h3)
    (by exact_mod_cast crudeBZ_le_KB_f1)

theorem wordBound_f2 : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famParts cert zmul 2 gs2 zsT zaT (eqLocF cert)) w0 w1 w2 w3| ≤ KB := fun w0 w1 w2 w3 h0 h1 h2 h3 =>
  le_trans (partsF_le_crudeBZ_eqLocF cert zmul 2 gs2 zsT zaT _ zqBmax_le_K w0 w1 w2 w3 h0 h1 h2 h3)
    (by exact_mod_cast crudeBZ_le_KB_f2)

theorem wordBound_prod : 24 * slen * KB < ps3.prod := by decide +kernel

theorem ps3_pos_le : ∀ p ∈ ps3, 0 < p ∧ p ≤ 2 ^ 600 := by decide +kernel

theorem crudeBMod_lt_f0 : crudeBMod cert 0 gs0 zsT zaT (2 ^ 600) < 2 ^ (bK - 1) := by decide +kernel
theorem crudeBMod_lt_f1 : crudeBMod cert 1 gs1 zsT zaT (2 ^ 600) < 2 ^ (bK - 1) := by decide +kernel
theorem crudeBMod_lt_f2 : crudeBMod cert 2 gs2 zsT zaT (2 ^ 600) < 2 ^ (bK - 1) := by decide +kernel

theorem wordBoundMod_f0 : ∀ p ∈ ps3, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famPartsMod p zmul cert 0 gs0 zsT zaT (eqLocF cert)) w0 w1 w2 w3| < 2 ^ (bK - 1) :=
  fun p hp w0 w1 w2 w3 h0 h1 h2 h3 =>
    lt_of_le_of_lt (partsF_le_crudeBMod_eqLocF p zmul cert 0 gs0 zsT zaT _ (ps3_pos_le p hp).1 (ps3_pos_le p hp).2
      w0 w1 w2 w3 h0 h1 h2 h3) (by exact_mod_cast crudeBMod_lt_f0)

theorem wordBoundMod_f1 : ∀ p ∈ ps3, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famPartsMod p zmul cert 1 gs1 zsT zaT (eqLocF cert)) w0 w1 w2 w3| < 2 ^ (bK - 1) :=
  fun p hp w0 w1 w2 w3 h0 h1 h2 h3 =>
    lt_of_le_of_lt (partsF_le_crudeBMod_eqLocF p zmul cert 1 gs1 zsT zaT _ (ps3_pos_le p hp).1 (ps3_pos_le p hp).2
      w0 w1 w2 w3 h0 h1 h2 h3) (by exact_mod_cast crudeBMod_lt_f1)

theorem wordBoundMod_f2 : ∀ p ∈ ps3, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famPartsMod p zmul cert 2 gs2 zsT zaT (eqLocF cert)) w0 w1 w2 w3| < 2 ^ (bK - 1) :=
  fun p hp w0 w1 w2 w3 h0 h1 h2 h3 =>
    lt_of_le_of_lt (partsF_le_crudeBMod_eqLocF p zmul cert 2 gs2 zsT zaT _ (ps3_pos_le p hp).1 (ps3_pos_le p hp).2
      w0 w1 w2 w3 h0 h1 h2 h3) (by exact_mod_cast crudeBMod_lt_f2)

end NPT.Cert.EP3D3
