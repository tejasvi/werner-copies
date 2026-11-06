/-
NPT.K4.DataK497 — the data conditions of the K4 @ 497 slice checks by kernel evaluation (no `native_decide`): the
statements of `NPT.K4.Route.T497.DataChkN` (suffix `K`), through the chunked lookups and the sorted item comparison of
`NPT.K4.DataK`.
-/
import NPT.K4.DataK
import NPT.K4.D3T497.SemData
import NPT.K4.Route.T497.Consts
import NPT.K4.Route.T497.RGrp0
import NPT.K4.Route.T497.RGrp1
import NPT.K4.Route.T497.RGrp2

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.K4.Route.T497

open NPT.Cert NPT.Cert.Ident NPT.Cert.Sem NPT.K4.Route NPT.K4.D3T497

/-- The type list in its chunks. -/
def typesCh : List (List TypeD) :=
  [types000, types001, types002, types003, types004, types005, types006, types007, types008, types009, types010, types011]

/-- The block list in its chunks. -/
def blocksCh : List (List PBlock) :=
  [blocks000, blocks001, blocks002, blocks003, blocks004, blocks005, blocks006, blocks007, blocks008, blocks009, blocks010]

lemma typesCh_flatten : typesCh.flatten = cert.types := by
  simp only [typesCh, cert, types, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

lemma blocksCh_flatten : blocksCh.flatten = cert.Z := by
  simp only [blocksCh, cert, blocks, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

lemma grpOK5_chunks : grpOK5 cert E0 =
    grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0 := by
  have ht : getDChunks default typesCh = fun i => cert.types.getD i default := by
    funext i; rw [getDChunks_eq, typesCh_flatten]
  have hb : getDChunks default blocksCh = fun i => cert.Z.getD i default := by
    funext i; rw [getDChunks_eq, blocksCh_flatten]
  rw [ht, hb]; funext G; exact grpOK5_L cert E0 G

theorem grpOKK_f0 :
    rgs0.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel
theorem grpOKK_f1 :
    rgs1.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel
theorem grpOKK_f2 :
    rgs2.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel

theorem grpOK5K_f0 : rgs0.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f0
theorem grpOK5K_f1 : rgs1.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f1
theorem grpOK5K_f2 : rgs2.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f2

theorem itemsSort_f0 : msortF lexLe 16 (rgs0.flatMap fun G => itemsOf G.tree) = allItemsL 0 cert.types 0 := by
  decide +kernel
theorem itemsSort_f1 : msortF lexLe 16 (rgs1.flatMap fun G => itemsOf G.tree) = allItemsL 1 cert.types 0 := by
  decide +kernel
theorem itemsSort_f2 : msortF lexLe 16 (rgs2.flatMap fun G => itemsOf G.tree) = allItemsL 2 cert.types 0 := by
  decide +kernel

theorem itemsPerm5K_f0 : (rgs0.flatMap fun G => itemsOf G.tree).Perm (allItems cert 0) :=
  items_perm_of_sort cert 0 rgs0 16 itemsSort_f0
theorem itemsPerm5K_f1 : (rgs1.flatMap fun G => itemsOf G.tree).Perm (allItems cert 1) :=
  items_perm_of_sort cert 1 rgs1 16 itemsSort_f1
theorem itemsPerm5K_f2 : (rgs2.flatMap fun G => itemsOf G.tree).Perm (allItems cert 2) :=
  items_perm_of_sort cert 2 rgs2 16 itemsSort_f2

theorem eqKinds5K : cert.eqs.all (fun g => g.parts.all fun P => (List.finRange 5).all fun l =>
    (P.specs.getD l.val default).kind == 0 || nf 4 3 l == 2) = true := by decide +kernel

end NPT.K4.Route.T497

#print axioms NPT.K4.Route.T497.grpOK5K_f1
#print axioms NPT.K4.Route.T497.itemsPerm5K_f1
#print axioms NPT.K4.Route.T497.eqKinds5K
