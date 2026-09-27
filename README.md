# Lean formalizations of Matrix Spencer and Kadison–Singer

These are the companion Lean formalization proofs of the results in the three papers in the series **“A Walk from Free Probability to Matrix Discrepancy”**.

Six Lean projects contain separate existence proofs and polynomial real-arithmetic algorithms for square/rectangular Matrix Spencer, rank-one Kadison–Singer, and higher-rank Kadison–Singer with a square-root-logarithmic rank bound. In the notation below, n counts inputs and m is the matrix dimension.

## Start here

| Folder | Contents | Public build target |
| --- | --- | --- |
| [existence_ms](existence_ms/README.md) | Matrix Spencer: existence | `FaithfulExistenceMS` |
| [ms](ms/README.md) | Matrix Spencer: polynomial arithmetic algorithms | `FaithfulMS` |
| [existence_ks](existence_ks/README.md) | Rank-one Kadison–Singer: existence | `FaithfulExistenceKS` |
| [ks](ks/README.md) | Rank-one Kadison–Singer: deterministic algorithm | `FaithfulKS` |
| [existence_higher_rank_ks](existence_higher_rank_ks/README.md) | Higher-rank Kadison–Singer: existence | `AugmentedHigherRankKS` |
| [higher_rank_ks](higher_rank_ks/README.md) | Higher-rank Kadison–Singer: deterministic algorithm | `HigherRankKSRuntime` |

Each linked README states the hypotheses, exact constants, computational assumptions, theorem locations, and audit commands. The existence statements assume only the mathematical input conditions. Runtime statements additionally require the stated SDP service and exact-EVD arithmetic model. MS is randomized with failure at most `2^(-k)`; both KS algorithms are deterministic.

The MS service returns an **exact primal optimizer** with polynomial work. KS services return **approximate values** with polynomial work in size and reciprocal accuracy. These contracts do not constitute implementations of SDP solvers. There is no binary bit-complexity claim.

## Install and build

Install [elan](https://github.com/leanprover/elan), Lean's toolchain manager, and put its bin directory on PATH. A POSIX shell and Git are needed; the initial dependency/cache download needs internet access. All projects pin Lean 4.24.0 and include Lake dependency lockfiles.

Clone the whole repository. To build one project, for example:

```sh
cd existence_ms
sh run_lake.sh exe cache get
sh run_lake.sh build FaithfulExistenceMS
sh run_lake.sh env lean FaithfulExistenceMS/Audit.lean
```

From the repository root, build all six (in dependency order):

```sh
sh build_all.sh --fetch-cache
```

For subsequent builds using installed dependencies:

```sh
sh build_all.sh
```

There is no root Lake project: `build_all.sh` enters each project. The higher-rank runtime project depends on its sibling `existence_higher_rank_ks`; retain that relative layout. Each project may maintain its own mathlib cache, so a complete build can require substantial disk space and time. Do not run `lake update` merely to build: keep the checked-in dependency revisions.

## How to read the proofs

Start with the linked public theorem file in the relevant README, then its audit and imported implementation modules. Public theorems distinguish existence, correctness of the computed output, probability, and counted work. A source file marked `noncomputable` can contain mathematical choices or definitions of idealized primitives; this repository is a proof development, not an extracted numerical application.

The [square implementation map](ms/SQUARE_CORRESPONDENCE.md), [rectangular implementation map](ms/RECTANGULAR_CORRESPONDENCE.md), and [higher-rank implementation map](higher_rank_ks/CORRESPONDENCE.md) describe the code paths and their interfaces.

## Verification

Run the build commands above and the audit command in each project README. [VERIFICATION.md](VERIFICATION.md) lists the targets. The higher-rank audit output is also available for [existence](existence_higher_rank_ks/audit_existence.txt) and [runtime](higher_rank_ks/audit_runtime.txt).

The allowed foundational axioms in the endpoint audits are `propext`, `Classical.choice`, and `Quot.sound`. Solver contracts appear as explicit parameters, not custom axioms. No favorable direction, successful walk, or unproved curvature estimate is supplied to the public endpoints.

[PACKAGING_VERIFICATION.md](PACKAGING_VERIFICATION.md) describes source-layout checks.

## Source layout

Use this folder's contents as the repository root. Keep all six projects, their source modules, toolchain files, Lake configuration/lockfiles, documentation, and audit records. The root `.gitignore` excludes build caches and OS/editor artifacts. It does not delete local caches. Review `git status --short` before committing; commit source files rather than generated build directories.
