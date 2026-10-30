# Local verification

These records concern this F2-only publication package and its two newly named
targets. No old combined-package Comparator receipt is reused as a new result.

| Check | Result | Record |
|---|---|---|
| Main and numerical proof entries | Pass | `library-build.log` |
| Ordinary build without Comparator | Pass | `ordinary-build.log` |
| Target axioms | Only `propext`, `Classical.choice`, `Quot.sound` | Both build logs |
| Reference signatures and 2,871 shared source copies | Pass | `input-check.json` |
| Public Linux Comparator and kernel replay | Pending at packaging time | [CI.md](CI.md) |
| Historical macOS replay | Exit code not recorded in the original receipt | `local-comparator-result.json`, `comparator.log` |
| Mathlib-only FC mathematical body | Pass | `fc-mathlib-only.log` |
| Seven simplified definitions agree with the previous FC definitions | Pass | `FCDefinitionEquivalence.lean`, `fc-simplification.log` |
| Official FC build/linter with the standard header | Pass | `fc-header-audit.log` |
| Canonical FC source with the short header | Fails copyright linter | `fc-short-header.log` |
| FC definitions to proof-library definitions | Not implemented | `../lean/comparator/TARGET-CORRESPONDENCE.md` |

The proof projects pin Lean `v4.35.0-rc3` and Mathlib
`f6090c7095e1e56b3464c1daba5f24631f1290d2`. The official FC audit pins
`c83a94d785d0fb3b9b9a2a94e8ffff8cce76a346`, Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

The macOS Comparator run disables its Linux-only sandbox and is not a sandboxed
Linux CI result. Dependency style and deprecation warnings remain in the proof
build logs; a warning-free build of the full dependency library is not claimed.

The FC file has seven definitions, no `variable` declarations, one instance and
two intentional problem-statement holes. The solution has no proof holes or custom
axioms. The FC checker returns failure when the canonical short-header file fails,
even if the temporary standard-header audit passes. It restores the canonical
source and does not disable any FC linter.

`FCDefinitionEquivalence.lean` contains both definition copies and proofs of their
agreement. Its copy of the current definitions is checked against the canonical
file. Reducibility attributes are attached when declaring the comparison copies
so rewrite tactics can compare the two namespaces; no unsafe-reducibility override
or kernel-check bypass is used. This compares FC representations, not the separate
proof library.

The parent prediction is restricted to complex projective pairs and integer
`a ≥ 1`. The `a = 0` case is not claimed. The numerical variant assumes no Iitaka
dimension, initial section or nonvanishing statement.

The two-page PDF is a statement and verification guide, not a full proof paper.
These are historical local receipts. Public CI is recorded separately in
[CI.md](CI.md), with the tested commit and workflow run. No upstream issue,
comment or PR has been posted as part of this publication.
