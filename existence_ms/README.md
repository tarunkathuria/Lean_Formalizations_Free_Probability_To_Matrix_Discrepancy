# Matrix Spencer: existence

[All projects and setup](../README.md)

## Public result

For real symmetric contractions, `FaithfulExistenceMS.exists_square` proves discrepancy at most `100000000 * sqrt(n)` when `m <= n`. `exists_rectangular` proves `100000000 * sqrt(n * log(2*m/n))` when `1 <= n <= m`. Here n counts matrices and m is their dimension.

Read the exact declarations in [FaithfulExistenceMS/Main.lean](FaithfulExistenceMS/Main.lean).

## Assumptions and scope

There is no solver, runtime, curvature, direction, or successful-walk assumption. Exact optimizers are selected mathematically from proved attainment. The proofs follow the direct-density projection walk.

Runtime claims concern counted exact-real arithmetic, not binary bit complexity, extracted executables, or an implementation of the supplied SDP/EVD primitives. Existence-only statements have no computational contract.

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and ensure `lake` is on PATH. The checked-in `lean-toolchain` selects Lean 4.24.0; `lake-manifest.json` pins dependency revisions. Run from this folder:

```sh
sh run_lake.sh exe cache get
sh run_lake.sh build FaithfulExistenceMS
sh run_lake.sh env lean FaithfulExistenceMS/Audit.lean
```

The first command downloads mathlib's compiled cache and requires network access. The build checks this public library and its dependencies; the audit prints/checks theorem assumptions. Recorded audits list only `propext`, `Classical.choice`, and `Quot.sound`; explicit solver parameters remain assumptions even when they do not appear in that axiom list.

## Navigation

[Algorithmic project](../ms/README.md); [scope](FAITHFUL_SCOPE.md).

Keep all shipped Lean source directories, including shared dependency modules. Generated `.lake/` and `.cache/` directories are not part of the source distribution.
