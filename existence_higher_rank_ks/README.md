# Higher-rank Kadison–Singer: existence

[All projects and setup](../README.md)

## Public result

`AugmentedHigherRankKS.subisotropic_existence` assumes complex PSD matrices, `sum A_i <= I`, operator norms at most epsilon, and ranks at most r, with `epsilon >= 0` and `r >= 1`. It proves one sign per original matrix with discrepancy at most `min 1 (10000 * sqrt(epsilon * log(2*r)))`. `existence` specializes to `sum A_i = I`.

Read the exact declarations in [AugmentedHigherRankKS/Existence.lean](AugmentedHigherRankKS/Existence.lean).

## Assumptions and scope

There are no solver, EVD, curvature, successful-epoch, or runtime assumptions. The proof uses the four-block discrepancy/budget potential, actual optimized densities, response estimates, compact reserve exhaustion, and finite epoch assembly. The HigherRankKS modules supply shared support; the public library is AugmentedHigherRankKS.

Runtime claims concern counted exact-real arithmetic, not binary bit complexity, extracted executables, or an implementation of the supplied SDP/EVD primitives. Existence-only statements have no computational contract.

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and ensure `lake` is on PATH. The checked-in `lean-toolchain` selects Lean 4.24.0; `lake-manifest.json` pins dependency revisions. Run from this folder:

```sh
sh run_lake.sh exe cache get
sh run_lake.sh build AugmentedHigherRankKS
sh run_lake.sh env lean AugmentedHigherRankKS/Audit.lean
```

The first command downloads mathlib's compiled cache and requires network access. The build checks this public library and its dependencies; the audit prints/checks theorem assumptions. Recorded audits list only `propext`, `Classical.choice`, and `Quot.sound`; explicit solver parameters remain assumptions even when they do not appear in that axiom list.

## Navigation

[Literal target statements](AugmentedHigherRankKS/Statement.lean); [algorithmic project](../higher_rank_ks/README.md); [recorded audit](audit_existence.txt).

Keep all shipped Lean source directories, including shared dependency modules. Generated `.lake/` and `.cache/` directories are not part of the source distribution.
