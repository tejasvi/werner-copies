# Final audit

The final audit rebuilt this package from scratch and checked the axioms of every theorem.

- **Sources.** A fresh copy of the source tree; every source file was hashed before the build. Every Lean file of this
  package has the audited SHA-256 and every module was built by the audit.
- **Toolchain.** Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), Mathlib commit
  `56a005855ea17e0b0958f73ec801ae140b0a1679` (build hash `359c60f733ecd8b8`), as pinned in `lean-toolchain` and
  `lake-manifest.json`.
- **Build.** 943 modules in topological import order, from an empty build directory, up to 24 at a time on a
  64-core x86-64 machine with 512 GB of RAM (sum of the address-space limits of the running modules ≤ 440 GiB),
  each under an address-space limit, with `maxHeartbeats 400000` and `Elab.async false`: 6.5 hours wall time,
  103 CPU-hours. Every module of the import order has a fresh `.olean` and no module build exited with an error.
  Largest modules: `D3T4979.Psd015` (41.4 GiB RSS, 48.2 GiB address space, 1978 s), `D3T497.Psd003` (40.9 GiB RSS, 49.7 GiB address space, 992 s), `D3T497.Psd009` (37.2 GiB RSS, 44.7 GiB address space, 1333 s). Slice checks: 72 checks, 14–27 min each, at most 5.9 GiB RSS and 14.9 GiB address space (`t = 497/1000`);
  120 checks, 12–62 min each, at most 7.9 GiB RSS and 19.0 GiB address space (`t = 4979/10000`).
- **Axioms.** `#print axioms` for the main theorems (below), for every theorem of `NPT.K4.Final497`,
  `NPT.K4.Final4979` and `NPT.K4.Werner4`, and for every theorem of every `NPT.*` module of the package
  (24760 theorems). 203 theorems use an axiom besides `propext`, `Classical.choice` and `Quot.sound`; every such
  axiom is one of the 192 `native_decide` axioms `NPT.K4.Route.T497.sliceOK{f}_{j}._native.native_decide.ax_1`
  and `NPT.K4.Route.T4979.sliceOK{f}_{j}._native.native_decide.ax_1` of the slice checks.
- **Text scan.** In the package's sources (the 943 files of the import order), `sorry` and `admit` occur only in comments
  (one line, in `NPT/Main.lean`, which says that `sorry` is not used), no source declares an axiom, and `native_decide`
  is used as a tactic in
  exactly the 192 slice-check modules `NPT/K4/Route/T497/Chk<f>_<j>.lean` and `NPT/K4/Route/T4979/Chk<f>_<j>.lean`
  (elsewhere the word occurs only in comments).

`#print axioms` of the main theorems: `AXIOMS_4979.txt` (`NPT.K4.D3T4979.EP_K4_4979`,
`NPT.K4.werner_four_copy_4979`: the standard axioms and 120 slice-check axioms) and `AXIOMS_497.txt`
(`NPT.K4.D3T497.EP_K4_497`: the standard axioms and 72 slice-check axioms).
