# Final audit

The final audit rebuilt this package from scratch and checked the axioms of every theorem.

- **Sources.** A fresh copy of the source tree; every source file was hashed before the build. Every Lean file of this
  package has the audited SHA-256 and every module was built by the audit.
- **Toolchain.** Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib commit
  `56a005855ea17e0b0958f73ec801ae140b0a1679`, as pinned in `lean-toolchain` and `lake-manifest.json`.
- **Build.** 961 modules in topological import order, from an empty build directory, up to 8 at a time, each
  under an address-space limit, with `maxHeartbeats 400000` and `Elab.async false`: 3.3 hours wall time,
  25 CPU-hours (for part of the run, a lower-priority sequential test build shared the machine). Largest
  modules: `EP3D4.KChkS<i>_1_1` (78.8 GiB RSS, 413 s), `EP3D3.KChkS<i>_1_1` (78.0 GiB RSS, 410 s), `EP3D4.KChk<i>_0` (74.5 GiB RSS, 373 s).
- **Axioms.** `#print axioms` for the main theorems (below), for every theorem of `NPT.Final` and `NPT.Main`, and for
  every theorem of every `NPT.*` module of the package (21,841 theorems): all depend only on `propext`,
  `Classical.choice` and `Quot.sound`. No theorem uses another axiom.
- **Text scan.** In the package's sources, the words `sorry`, `admit` and `native_decide` occur only in comments
  (20 lines, which say that they are not used or mention an earlier version of the identity facts that
  is not part of this package).

`#print axioms` of the main theorems:

```
'NPT.Cert.EP3_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3_d4' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3_d5' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3_d6' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3_d7' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3_d8' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.EP2_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.EP3_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.werner_three_copy_d3'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3D3.idFact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3D4.idFact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3D5.idFact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3D6.idFact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3D7.idFact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.EP3D8.idFact' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NPT.Cert.soundness_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
```
