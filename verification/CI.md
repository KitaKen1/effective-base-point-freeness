# Public CI

**Pass**, verified at `2026-10-31T04:05:00+00:00`.

- [Public GitHub Actions run](https://github.com/KitaKen1/effective-base-point-freeness/actions/runs/41138711113)
- Proof/source commit: `c59f4ead8983046e2684d97c333559842948f1bf`
- Run ID: `41138711113`, attempt `1`.
- [Downloaded verification evidence](public-ci-evidence.json).

| Check | Result |
|---|---|
| Identical proof sources and independent reference | Pass |
| Ordinary proof build and target axiom audit | Pass |
| Canonical solution, reference build and axiom audit | Pass |
| Source-bound checkpoints and export hashes | Pass |
| Native Comparator with Linux bubblewrap | Pass |
| Default Lean kernel replay | Accepted |

Both target declarations use exactly `propext`, `Classical.choice` and
`Quot.sound`. The downloaded native Comparator log contains both
`Lean default kernel accepts the solution` and `Your solution is okay!`,
with no sandbox-disabled warning.

The three-job workflow compiles the ordinary proof, verifies and restores that
source-bound checkpoint for the canonical build, exports both environments,
and runs native `lake comparator --challenge-from-export ...
--solution-from-export ...` in the final job. Source, toolchain, configuration,
archive and export hashes are checked before reuse. Mathematical type, dependency,
axiom and default-kernel checks remain enabled. The source fingerprint is
`5a92801be8a12b8717d4d772cfd355d62d2f41a61d86a54dc4984ab19ef66ebe`.

This is a **tentative public version**. The result covers the two library-backed
targets `EffectiveFreenessPublication.kollar` and
`EffectiveFreenessPublication.variants.numerical`. The standalone FC file retains
two intentional problem-statement holes; a Lean dictionary from its definitions
to the proof-library definitions is not implemented. Its requested short
copyright header also fails the strict FC copyright linter. Passing this proof
CI does not close that separate FC representation gap, and is not an independent
mathematical peer review.

Historical local receipts retain their original timestamps, status and process
exit-code information. This public Linux run is recorded separately. Verification
logs are retained in Actions artifacts for 14 days; compiled checkpoints and
exports are retained for one day. Documentation-only result commits use
`[skip ci]`; the source commit above identifies the verified run.

No upstream issue, comment or PR was posted.
