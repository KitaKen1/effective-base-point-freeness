> **Tentative version.** The official version will be released soon.

# Effective base point freeness and its numerical variant

[![Lean verification](https://github.com/KitaKen1/effective-base-point-freeness/actions/workflows/lean.yml/badge.svg)](https://github.com/KitaKen1/effective-base-point-freeness/actions/runs/41138711113)

Lean proofs of the complex projective, integral-parameter case of the linear
effective-freeness prediction in Kollár (1993), and a numerical-dimension variant (F2).

Let $(X,\Delta)$ be a normal complex projective klt pair of dimension $n$, with
effective rational boundary. Let $D$ be nef Cartier and let $a\ge1$ be an integer.
Assume that $aD-(K_X+\Delta)$ is nef and big.

**Main statement.** $(a+n+1)D$ is globally generated.
This is the above restricted case of the prediction stated after Theorem 1.1 on
page 596 of [Kollár, *Effective base point freeness*](https://doi.org/10.1007/BF01445123).

**Numerical variant (F2).** For every integer $m\ge a+\nu(D)+1$, $mD$ is globally
generated. Moreover, $\nu(D)=0$ implies $D\sim0$. Here

$$\nu(D)=\max\{k\in\{0,\ldots,n\}:D^k\cdot J^{n-k}>0\},$$

where $J$ is ample Cartier. Since $\nu(D)\le n$, F2 implies the main statement by
taking $m=a+n+1$. This implication is proved in Lean.

The scope restriction matters: Kollár's setting allows $a\ge0$, proper varieties
and characteristic-zero fields. This package does not claim that full range.
The numerical bound, all-multiples conclusion and numerical-zero conclusion are
this project's variant; they are not attributed verbatim to Kollár or OpenAI.

## Proof entries

| Entry | Declaration |
|---|---|
| Restricted linear prediction | `EffectiveFreenessPublication.kollar` |
| Numerical variant, including numerical zero | `EffectiveFreenessPublication.variants.numerical` |

[FCSolution.lean](lean/FCSolution.lean) supplies both proofs.
[Challenge.lean](lean/Challenge.lean) is a separate statement reference whose import
closure excludes the solution and the final effective-freeness proof module.
The solution targets use only `propext`, `Classical.choice` and `Quot.sound`.
The reference's two statement holes are intentional; the solution has none.

F2 derives nonvanishing and the equality $\kappa(D)=\nu(D)$ internally. Neither is
an input hypothesis. The proof covers dimension zero and proves the principal
divisor conclusion in the numerical-zero case.

## Files

| Directory | Contents |
|---|---|
| [lean/](lean/) | Proof, independent Challenge, axiom audit and Comparator configuration |
| [leanWithoutComparator/](leanWithoutComparator/) | The same proof sources with an ordinary Lake build |
| [FClikelean/EffectiveFreeness.lean](FClikelean/EffectiveFreeness.lean) | One-file FC statement: main item and `variants.numerical` |
| [PDF/](PDF/) | Two-page statement and verification guide |
| [verification/](verification/) | Local results, source review and scope |
| [PR-DRAFT.md](PR-DRAFT.md) | Local FC pull request draft |

The package contains the 2,868 local library modules needed by its proof imports.
The 2,871 shared Lean sources in the proof directories are byte-identical. F1's
publication targets are outside this package; some foundational proofs are shared.

## Local checks

The proof projects pin Lean `v4.35.0-rc3` and Mathlib
`f6090c7095e1e56b3464c1daba5f24631f1290d2`.

```sh
cd leanWithoutComparator
lake exe cache get
lake build
```

From the package root:

```sh
python3 lean/comparator/check-inputs.py
```

On Linux with bubblewrap available:

```sh
cd lean
lake exe cache get
lake comparator
```

See the [Comparator guide](lean/comparator/README.md) for the macOS procedure.
The records distinguish ordinary builds, source checks, native Comparator replay
and the separate FC audit. An older combined F1/F2 receipt is not a result for
these newly named targets. Local `.lake` caches are ignored.

## Standalone FC file

[EffectiveFreeness.lean](FClikelean/EffectiveFreeness.lean) has seven definitions,
no `variable` declarations, one instance and two intentional statement holes.
Its only import is `FormalConjecturesUtil`; its mathematical body also elaborates
with only Mathlib. It imports no project, TauCeti or OAI library.

The instance supplies the complex algebra structure for relative differentials.
The section space is the complex span of regular rational sections, avoiding
extra stalk-algebra and scalar-tower declarations. Local differential lattices
and the change of rational volume form are contained inside `EffectiveKlt`.
The agreement with the preceding FC definitions is proved in
[FCDefinitionEquivalence.lean](verification/FCDefinitionEquivalence.lean).

The problem file and proof library use different representations of divisors,
sections and numerical intersections. A Lean dictionary between them is not yet
established. The FC draft therefore keeps `category research open` and has no
`formal_proof` link. See [the correspondence review](lean/comparator/TARGET-CORRESPONDENCE.md).

The official FC audit pins commit
`c83a94d785d0fb3b9b9a2a94e8ffff8cce76a346`, Lean `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`.

```sh
python3 lean/comparator/check-fclike.py --fc-root /path/to/formal-conjectures
```

The short project copyright header is retained as requested. FC's strict
copyright linter requires its longer template. The checker records the canonical
short-header result and a separate temporary standard-header audit, restores the
source, and returns failure if the canonical file fails. No FC linter is disabled.

The PDF is a guide, not a full proof paper. Its ReportLab source is
`verification/make-guide.py` and uses the named macOS system fonts.

## Sources and attribution

[Kollár (1993), pp.595–596](https://gdz.sub.uni-goettingen.de/download/pdf/PPN235181684_0296/LOG_0036.pdf#page=3)
is the source of the parent prediction. The sharp linear bound is stated after
Theorem 1.1; the larger bound proved in Theorem 1.1 is a different statement.

[Fujino, Theorem 2.1](https://www.math.kyoto-u.ac.jp/preprint/2011/03fujino.pdf)
is background for qualitative klt base-point freeness. It does not state the F2
coefficient. [OpenAI's 2026 Fujita manuscript](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Fujitas-freeness-conjecture-September-23-2026)
claims a proof of classical smooth Fujita freeness; its minimization,
center-exclusion and lifting strategy informed this development. It is not cited
as an original statement or a Lean proof of F2.

Kenta Kitamura developed this project with assistance from ChatGPT and OpenAI Codex.
No independent mathematical peer review is claimed. Machine checks, source
attribution and the correspondence with natural language are separate checks.

Project code is Apache-2.0; vendored libraries retain their notices and licenses,
including MIT for SGA. See [LICENSE](LICENSE) and [vendor](lean/vendor/).
The historical local receipts describe the earlier local checks. Public CI is
recorded separately in [verification/CI.md](verification/CI.md), with the tested
commit and downloaded verification evidence. No upstream issue, comment or PR
was posted as part of this publication.
