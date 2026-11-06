/-
NPT.K4.DataK4979 — the data conditions of the five-family (K4 @ 4979/10000) slice checks by kernel evaluation (no
`native_decide`): every item of every rule group (families 0..4) has the group's tree modules, rule and family,
n = 3/3/3/3/2, no correction entries and exponent 254 (`grpOK5K_f<f>`, through the chunked lookups of `NPT.K4.DataK`);
the groups' items are a permutation of the family's multiplier entries (`itemsPerm5K_f<f>`, fuelled merge sort);
kind-1 equality specs only sit on the auxiliary leg (`eqKinds5K`).
-/
import NPT.K4.DataK
import NPT.K4.D3T4979.SemData
import NPT.K4.Route.T4979.Consts
import NPT.K4.Route.T4979.RGrp0
import NPT.K4.Route.T4979.RGrp1
import NPT.K4.Route.T4979.RGrp2
import NPT.K4.Route.T4979.RGrp3
import NPT.K4.Route.T4979.RGrp4

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.K4.Route.T4979

open NPT.Cert NPT.Cert.Ident NPT.Cert.Sem NPT.K4.Route NPT.K4.D3T4979

/-- The type list in its chunks. -/
def typesCh : List (List TypeD) :=
  [types000, types001, types002, types003, types004, types005, types006, types007, types008, types009, types010, types011, types012, types013, types014, types015, types016, types017, types018, types019, types020, types021, types022, types023, types024, types025, types026, types027, types028, types029, types030, types031, types032, types033, types034, types035, types036]

/-- The block list in its chunks. -/
def blocksCh : List (List PBlock) :=
  [blocks000, blocks001, blocks002, blocks003, blocks004, blocks005, blocks006, blocks007, blocks008, blocks009, blocks010, blocks011, blocks012, blocks013, blocks014, blocks015, blocks016, blocks017, blocks018, blocks019, blocks020]

lemma typesCh_flatten : typesCh.flatten = cert.types := by
  simp only [typesCh, cert, types, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

lemma blocksCh_flatten : blocksCh.flatten = cert.Z := by
  simp only [blocksCh, cert, blocks, List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

lemma grpOK5_chunks (E0 : ℕ) : grpOK5 cert E0 =
    grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0 := by
  have ht : getDChunks default typesCh = fun i => cert.types.getD i default := by
    funext i; rw [getDChunks_eq, typesCh_flatten]
  have hb : getDChunks default blocksCh = fun i => cert.Z.getD i default := by
    funext i; rw [getDChunks_eq, blocksCh_flatten]
  rw [ht, hb]; funext G; exact grpOK5_L cert E0 G

theorem eqKinds5K : cert.eqs.all (fun g => g.parts.all fun P => (List.finRange 5).all fun l =>
    (P.specs.getD l.val default).kind == 0 || nf 4 3 l == 2) = true := by decide +kernel

theorem grpOKK_f0 :
    rgs0.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel
theorem grpOKK_f1 :
    rgs1.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel
theorem grpOKK_f2 :
    rgs2.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel
theorem grpOKK_f3 :
    rgs3.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel
theorem grpOKK_f4 :
    rgs4.all (grpOKL (getDChunks default typesCh) (getDChunks default blocksCh) cert.mods cert.d E0) = true := by
  decide +kernel

theorem grpOK5K_f0 : rgs0.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f0
theorem grpOK5K_f1 : rgs1.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f1
theorem grpOK5K_f2 : rgs2.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f2
theorem grpOK5K_f3 : rgs3.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f3
theorem grpOK5K_f4 : rgs4.all (grpOK5 cert E0) = true := by rw [grpOK5_chunks]; exact grpOKK_f4

theorem itemsSort_f0 : msortF lexLe 16 (rgs0.flatMap fun G => itemsOf G.tree) = allItemsL 0 cert.types 0 := by
  decide +kernel
theorem itemsSort_f1 : msortF lexLe 16 (rgs1.flatMap fun G => itemsOf G.tree) = allItemsL 1 cert.types 0 := by
  decide +kernel
theorem itemsSort_f2 : msortF lexLe 16 (rgs2.flatMap fun G => itemsOf G.tree) = allItemsL 2 cert.types 0 := by
  decide +kernel
theorem itemsSort_f3 : msortF lexLe 16 (rgs3.flatMap fun G => itemsOf G.tree) = allItemsL 3 cert.types 0 := by
  decide +kernel
theorem itemsSort_f4 : msortF lexLe 16 (rgs4.flatMap fun G => itemsOf G.tree) = allItemsL 4 cert.types 0 := by
  decide +kernel

theorem itemsPerm5K_f0 : (rgs0.flatMap fun G => itemsOf G.tree).Perm (allItems cert 0) :=
  items_perm_of_sort cert 0 rgs0 16 itemsSort_f0
theorem itemsPerm5K_f1 : (rgs1.flatMap fun G => itemsOf G.tree).Perm (allItems cert 1) :=
  items_perm_of_sort cert 1 rgs1 16 itemsSort_f1
theorem itemsPerm5K_f2 : (rgs2.flatMap fun G => itemsOf G.tree).Perm (allItems cert 2) :=
  items_perm_of_sort cert 2 rgs2 16 itemsSort_f2
theorem itemsPerm5K_f3 : (rgs3.flatMap fun G => itemsOf G.tree).Perm (allItems cert 3) :=
  items_perm_of_sort cert 3 rgs3 16 itemsSort_f3
theorem itemsPerm5K_f4 : (rgs4.flatMap fun G => itemsOf G.tree).Perm (allItems cert 4) :=
  items_perm_of_sort cert 4 rgs4 16 itemsSort_f4

end NPT.K4.Route.T4979

#print axioms NPT.K4.Route.T4979.grpOK5_chunks
#print axioms NPT.K4.Route.T4979.eqKinds5K
#print axioms NPT.K4.Route.T4979.grpOK5K_f1
#print axioms NPT.K4.Route.T4979.itemsPerm5K_f1
#print axioms NPT.K4.Route.T4979.itemsPerm5K_f3
