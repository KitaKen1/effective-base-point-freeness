# Resumable public verification

The workflow separates proof compilation, export and comparison so that each
stage has its own job time allowance. Completed source-bound build caches also
allow a timed-out compilation to resume.

The workflow has three jobs:

1. Build `leanWithoutComparator` and audit both target axioms. Save the completed
   build as an artifact, and also save partial compilation progress in a cache.
2. Check the source fingerprint and restore that build into `lean`. Build the
   canonical solution and independent `Challenge`, recheck the target axioms,
   and export both environments with the pinned bundled `leanexport`.
3. Verify source/configuration hashes and both export checksums, then run native
   `lake comparator` with `--challenge-from-export` and `--solution-from-export`.
   The Linux bubblewrap sandbox and default kernel replay remain enabled.

Using exports changes where compilation takes place. It does not remove target
type comparison, dependency comparison, axiom restrictions, or kernel checking.
Both default-kernel acceptance and Comparator success must appear in the log;
an exit code alone is not used to claim success, and a sandbox-disabled warning
is rejected.

The checkpoint key covers both proof-source trees, Lake configurations and lock
files, the Lean toolchain, and Comparator configuration. It excludes `.lake`
outputs. The existing source audit still requires byte-identical proof copies,
an independent reference import closure, and no proof holes or custom axioms in
the proof sources. Artifacts have independent SHA-256 checks before reuse.

Compiled build/export artifacts are retained for one day. Small
verification logs are retained for 14 days. A failed or timed-out proof build
does not permit downstream comparison to run; a subsequent run can reuse its
partial cache and must still complete the actual build and audits.

Build/export jobs keep the runner's default swap and delete the compressed
checkpoint after restoration, leaving space for Mathlib and both exports. The
final Comparator job reserves 12 GiB of additional swap; it does not download or
rebuild Mathlib. These resource settings leave all mathematical checks enabled.

The standalone FC definitions remain outside this proof claim. Their dictionary
to the proof library is not established. No theorem statement, proof source,
allowed axiom, upstream issue, or repository visibility is changed here.
