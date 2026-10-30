# Public CI

This is a tentative public version of the F2 proof package.

The [public Actions workflow](https://github.com/KitaKen1/effective-base-point-freeness/actions)
builds the ordinary proof, audits both target axioms, restores a source-bound
checkpoint for the canonical solution and independent reference, and exports
both environments. The final job verifies both export hashes and runs native
Comparator with the Linux bubblewrap sandbox and default Lean kernel replay.

The initial public run is pending at packaging time. Its URL, tested commit,
job outcomes and downloaded verification evidence will be recorded here after
execution. Historical local receipts are not presented as public CI results.

The standalone FC file retains two intentional statement holes. The Lean
dictionary connecting its definitions to the proof-library definitions is not
implemented. Its requested short copyright header also fails the strict FC
copyright linter. This proof CI does not complete that separate FC connection.

No upstream issue, comment or PR is posted by this workflow.
