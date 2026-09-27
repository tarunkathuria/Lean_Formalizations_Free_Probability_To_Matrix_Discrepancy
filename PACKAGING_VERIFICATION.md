# Source layout checks

Each project contains a Lake configuration, dependency lockfile, toolchain file, portable launcher, and README. The higher-rank runtime project has one relative dependency on `../existence_higher_rank_ks`; retain the sibling layout.

Generated `.lake/`, `.cache/`, Python caches, and OS metadata are excluded by the root `.gitignore`. All other Lean source directories are retained, including shared dependencies. The build scripts use `lake` on PATH and select the toolchain from each project directory.
