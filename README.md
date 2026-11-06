# Undistillability of Werner states from three, four and five copies

Programs and Lean 4 proofs for version 5 of the paper of this title. The paper and the full verification packages are
on Zenodo:

- version 5: https://doi.org/10.5281/zenodo.23992387
- all versions: https://doi.org/10.5281/zenodo.23604343

Each directory below is one package of that record, unpacked. The certificate and data files (`*.pkl`, `*.xz`, `*.npy`
and `release_allk/certs/`) are left out. Every other file is identical to the one in the archive, and each package's
`SHA256SUMS` also lists the files left out here.

| Directory | Package |
|---|---|
| `release_lean` | Lean 4 formalization: three-copy endpoint property of Werner states (EP_3, d = 3..8) |
| `release_lean_k4` | Lean 4 formalization: four-copy endpoint property of Werner states at d = 3 (EP_4, t = 4979/10000 and 497/1000) |
| `release_ep3` | EP_3 for every local dimension d ≥ 3 — compact certificate and standalone verifier |
| `release_ep3_checks` | EP_3 for every local dimension d ≥ 3 — additional cross-checks: code, data and reference logs |
| `release_k4` | Exact certificates for four copies of a qutrit (k = 4, d = 3) at t = 49/100, 99/200, 62/125, 497/1000, 2489/5000 and 4979/10000 |
| `release_k5` | Exact certificates for five copies of a qutrit (k = 5, d = 3) at t = 9/20 and 47/100 |
| `release_k4alld` | Four-copy Werner undistillability for α ≥ −79/160 in every dimension: exact verification package |
| `release_k5alld` | Five-copy Werner undistillability for α ≥ −9/20 in every dimension: exact verification package |
| `release_allk` | k-copy Werner undistillability for α ≥ −11/(5k) in every dimension: exact verification package |

## How to check

The two Lean packages are complete here. Build one with `./build_sequential.sh` in its directory, as its README
describes (`release_lean/README.md`, `release_lean_k4/README_k4.md`); the README also gives the memory and time the build
needs.

The other packages need the files left out here, so check them from the archives. Download an archive from the
[v5 release](https://github.com/tejasvi/werner-copies/releases/tag/v5) of this repository or from Zenodo, compare its
SHA-256 with the list in the release notes, unpack it and follow its README:

    sha256sum release_k4.tar.gz
    tar -xzf release_k4.tar.gz
    cd release_k4

`release_ep3_checks.tar.gz` (2.5 GB) is over GitHub's size limit for release files, so it is only on Zenodo.

## License

Every package is licensed under CC BY 4.0; see the `LICENSE` file in its directory.
