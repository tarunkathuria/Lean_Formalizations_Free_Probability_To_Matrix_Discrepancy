# Build and theorem checks

From the repository root, `sh build_all.sh` builds each default public library in dependency order. Use `sh build_all.sh --fetch-cache` to fetch dependency caches first.

| Project | Public library | Audit file (relative to project) |
| --- | --- | --- |
| existence_ms | FaithfulExistenceMS | FaithfulExistenceMS/Audit.lean |
| ms | FaithfulMS | FaithfulMS/MainAudit.lean |
| existence_ks | FaithfulExistenceKS | FaithfulExistenceKS/Audit.lean |
| ks | FaithfulKS | FaithfulKS/Audit.lean |
| existence_higher_rank_ks | AugmentedHigherRankKS | AugmentedHigherRankKS/Audit.lean |
| higher_rank_ks | HigherRankKSRuntime | Audit.lean |

Within a project, run `sh run_lake.sh env lean <audit-file>` after building. These audits inspect public statements and axiom dependencies; they are not an independent implementation of the Lean kernel. Explicit solver parameters are part of theorem statements and are not listed as axioms by `#print axioms`.

The projects pin their Lean and dependency versions using `lean-toolchain` and `lake-manifest.json`. Successful cached builds check the dependency graph; a fresh build additionally reconstructs missing compiled artifacts. Build warnings about unused variables do not indicate proof admissions.
