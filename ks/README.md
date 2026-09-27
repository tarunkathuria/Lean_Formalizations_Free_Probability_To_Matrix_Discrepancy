# Rank-one Kadison–Singer: deterministic algorithm

[All projects and setup](../README.md)

## Public result

`FaithfulKS.polynomial_runtime_and_correctness` assumes complex isotropic vectors with squared norms at most epsilon. The same computed signing has discrepancy at most `35 * sqrt(epsilon)` and executed work bounded by one natural-coefficient polynomial in n and m. This is deterministic and includes zero dimensions.

Read the exact declarations in [FaithfulKS/Main.lean](FaithfulKS/Main.lean).

## Assumptions and scope

The explicit polynomial SDP-value solver provides additive-error reports, with work polynomial in data size and reciprocal accuracy. Exact EVD is a unit-invocation-cost arithmetic primitive. The proof derives query accuracy, finite-difference Hessian error, tangent-frame construction, radial progress, rounding, termination, and work bounds. No curvature or successful-output oracle is supplied.

Runtime claims concern counted exact-real arithmetic, not binary bit complexity, extracted executables, or an implementation of the supplied SDP/EVD primitives. Existence-only statements have no computational contract.

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and ensure `lake` is on PATH. The checked-in `lean-toolchain` selects Lean 4.24.0; `lake-manifest.json` pins dependency revisions. Run from this folder:

```sh
sh run_lake.sh exe cache get
sh run_lake.sh build FaithfulKS
sh run_lake.sh env lean FaithfulKS/Audit.lean
```

The first command downloads mathlib's compiled cache and requires network access. The build checks this public library and its dependencies; the audit prints/checks theorem assumptions. Recorded audits list only `propext`, `Classical.choice`, and `Quot.sound`; explicit solver parameters remain assumptions even when they do not appear in that axiom list.

## Navigation

[Existence project](../existence_ks/README.md); [scope](FAITHFUL_SCOPE.md); [solver contract](MatrixSpencer/KSPolynomialConvexSolver.lean).

Keep all shipped Lean source directories, including shared dependency modules. Generated `.lake/` and `.cache/` directories are not part of the source distribution.
