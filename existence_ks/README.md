# Rank-one Kadison–Singer: existence

[All projects and setup](../README.md)

## Public result

`FaithfulExistenceKS.exists_signing` assumes complex vectors with `sum v_i v_i* = I`, `epsilon >= 0`, and squared Euclidean norms at most epsilon. It proves one sign per original vector and operator discrepancy at most `35 * sqrt(epsilon)`, including zero dimensions.

Read the exact declarations in [FaithfulExistenceKS/Main.lean](FaithfulExistenceKS/Main.lean).

## Assumptions and scope

The statement has no computational primitive or runtime assumption. Its proof follows the radial walk using variational values obtained from proved attainment.

Runtime claims concern counted exact-real arithmetic, not binary bit complexity, extracted executables, or an implementation of the supplied SDP/EVD primitives. Existence-only statements have no computational contract.

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and ensure `lake` is on PATH. The checked-in `lean-toolchain` selects Lean 4.24.0; `lake-manifest.json` pins dependency revisions. Run from this folder:

```sh
sh run_lake.sh exe cache get
sh run_lake.sh build FaithfulExistenceKS
sh run_lake.sh env lean FaithfulExistenceKS/Audit.lean
```

The first command downloads mathlib's compiled cache and requires network access. The build checks this public library and its dependencies; the audit prints/checks theorem assumptions. Recorded audits list only `propext`, `Classical.choice`, and `Quot.sound`; explicit solver parameters remain assumptions even when they do not appear in that axiom list.

## Navigation

[Algorithmic project](../ks/README.md); [scope](FAITHFUL_SCOPE.md).

Keep all shipped Lean source directories, including shared dependency modules. Generated `.lake/` and `.cache/` directories are not part of the source distribution.
