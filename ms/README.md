# Matrix Spencer: polynomial arithmetic algorithms

[All projects and setup](../README.md)

## Public result

`FaithfulMS.Main.matrix_spencer_square` and `matrix_spencer_rectangular` allow complex Hermitian contractions. Their respective bounds are `10651761 * sqrt(n)` for `m <= n` and `8102676 * sqrt(n*(1+log(2*m/n)))` for `1 <= n <= m`. For each confidence parameter k, success probability is at least `1-2^(-k)`. A single bound `C*(n+m+k+2)^e` controls operations and draws on every execution, including unsuccessful runs.

Read the exact declarations in [FaithfulMS/Main.lean](FaithfulMS/Main.lean).

## Assumptions and scope

The supplied `DirectSDP.PolynomialService` returns an exact attained primal SDP optimizer with polynomial work in data size. Exact EVD is an arithmetic primitive. These are explicit idealizations, not an implementation of an ellipsoid/IPM solver. Density extraction, Gamma, preparation, uniform projection sampling, acceptance, and adaptive probability/work accounting are proved. Covariance cleanup uses finite Jacobi rotations and Schur deletions; scalar step schedules are explicitly defined and bounded.

Runtime claims concern counted exact-real arithmetic, not binary bit complexity, extracted executables, or an implementation of the supplied SDP/EVD primitives. Existence-only statements have no computational contract.

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and ensure `lake` is on PATH. The checked-in `lean-toolchain` selects Lean 4.24.0; `lake-manifest.json` pins dependency revisions. Run from this folder:

```sh
sh run_lake.sh exe cache get
sh run_lake.sh build FaithfulMS
sh run_lake.sh env lean FaithfulMS/MainAudit.lean
```

The first command downloads mathlib's compiled cache and requires network access. The build checks this public library and its dependencies; the audit prints/checks theorem assumptions. Recorded audits list only `propext`, `Classical.choice`, and `Quot.sound`; explicit solver parameters remain assumptions even when they do not appear in that axiom list.

## Navigation

[Existence project](../existence_ms/README.md); [square correspondence](SQUARE_CORRESPONDENCE.md); [rectangular correspondence](RECTANGULAR_CORRESPONDENCE.md); [solver contract](FaithfulMS/DirectSDP.lean).

Keep all shipped Lean source directories, including shared dependency modules. Generated `.lake/` and `.cache/` directories are not part of the source distribution.
