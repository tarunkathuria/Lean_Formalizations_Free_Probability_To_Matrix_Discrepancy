# Higher-rank Kadison–Singer: deterministic algorithm

[All projects and setup](../README.md)

## Public result

`HigherRankKSRuntime.algorithmic` assumes complex PSD matrices with `sum A_i = I`, norms at most epsilon, and ranks at most r (`epsilon >= 0`, `r >= 1`). The deterministic computed output has discrepancy at most `min 1 (10000 * sqrt(epsilon * log(2*r)))` and cost at most `C*(1+n+m)^e`. The constants are fixed with the solver, independently of entries, epsilon, and r. The public runtime theorem requires isotropy; the separate existence theorem also covers subisotropy.

Read the exact declarations in [HigherRankKSRuntime/Main.lean](HigherRankKSRuntime/Main.lean).

## Assumptions and scope

The explicit SDP-value solver supplies additive accuracy and polynomial work in data size and reciprocal accuracy; its contract includes real-coordinate materialization of the specified affine-block SDP. Input factors, centers, reserves, and the walk are computed separately. Exact EVD is a unit-invocation-cost primitive. Local analysis, numerical tolerances, tangent directions, finite execution, and global work are proved.

Runtime claims concern counted exact-real arithmetic, not binary bit complexity, extracted executables, or an implementation of the supplied SDP/EVD primitives. Existence-only statements have no computational contract.

## Build and inspect

Install [elan](https://github.com/leanprover/elan) and ensure `lake` is on PATH. The checked-in `lean-toolchain` selects Lean 4.24.0; `lake-manifest.json` pins dependency revisions. Run from this folder:

```sh
sh run_lake.sh exe cache get
sh run_lake.sh build HigherRankKSRuntime
sh run_lake.sh env lean Audit.lean
```

The first command downloads mathlib's compiled cache and requires network access. The build checks this public library and its dependencies; the audit prints/checks theorem assumptions. Recorded audits list only `propext`, `Classical.choice`, and `Quot.sound`; explicit solver parameters remain assumptions even when they do not appear in that axiom list.

Keep this folder beside `existence_higher_rank_ks`: Lake uses the relative dependency `../existence_higher_rank_ks`.

## Navigation

[Existence project](../existence_higher_rank_ks/README.md); [algorithm correspondence](CORRESPONDENCE.md); [solver contract](HigherRankKSRuntime/RuntimeSDPValue.lean); [recorded audit](audit_runtime.txt).

Keep all shipped Lean source directories, including shared dependency modules. Generated `.lake/` and `.cache/` directories are not part of the source distribution.
