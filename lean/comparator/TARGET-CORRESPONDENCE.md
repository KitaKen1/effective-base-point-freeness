# Statement correspondence

The main target is a restriction of the linear prediction on p.596 of Kollár's
*Effective base point freeness* (1993), after Theorem 1.1. The numerical theorem
is this project's variant. It implies the restricted main target.

| Clause | Library reference and solution |
|---|---|
| Complex projective normal variety | Integral locally Noetherian scheme over `Spec ℂ`, proper, with an ample Cartier divisor `J` and integrally closed stalks |
| Dimension | `topologicalKrullDim X = n`; dimension zero is included |
| Effective rational klt boundary | `LogPairBoundaryEffective` and `LogPairIsKlt`, using a rational volume form and a positive Cartier denominator `r` |
| Auxiliary canonical data | A reference étale chart `c₀` and rational function `f₀`; these specify the canonical divisor |
| Nef Cartier divisor | `CartierIsNef ℂ D` |
| Adjoint difference nef and big | `CartierIsNef` and `CartierIsBig` for `(r*a)D − D'`, where `D'/r = K_X + Δ` |
| Integral parameter | `a : ℕ`, `1 ≤ a` |
| Main conclusion | Actual global sections generate `(a+n+1)D` at every point |
| Numerical variant | All `m ≥ a + cartierNumericalDimension D J + 1` work |
| Numerical zero | An actual equality to a principal Cartier divisor |
| Iitaka dimension / nonvanishing | Derived internally; absent from the target hypotheses |

The reference and solution signatures agree exactly. In `FCSolution.lean`, the
main target applies `variants.numerical` at `m = a+n+1` and uses the proved
inequality `cartierNumericalDimension_le_dim`.

## Restriction of the historical prediction

Kollár works in characteristic zero with proper klt pairs and `a ≥ 0`. The
present main target is explicitly limited to complex projective pairs, effective
rational boundaries and integer `a ≥ 1`. In particular, the package does not
claim the `a = 0` case or a complete proof of the original unrestricted statement.
The original sentence asks for the single coefficient `a+n+1`; the numerical
variant's all-multiples conclusion is additional.

## Separate FC representation

The standalone file represents Cartier divisors by compatible local equations.
Its rational section space is the complex span of functions regular after
multiplication by those equations. These functions already form a complex vector
space; using their span avoids extra public scalar-structure declarations.

`EffectiveKlt` encodes boundary effectivity at codimension-one points and
discrepancy greater than `−1` on all smooth proper birational models. The
function-field isomorphism is required to commute with the map of stalks.
Differential lattices and Jacobian determinants are local helpers inside that
definition, not abstract geometric predicates supplied as assumptions.

The finite difference of ample-twisted section dimensions detects
`D^k · J^(n-k)`. Serre vanishing identifies these section dimensions with Euler
characteristics for sufficiently large twists; the top finite difference is the
intersection number. The maximum ranges over `0 ≤ k ≤ n`. Its default value is
zero, and the ample `J` gives a positive zeroth intersection. No Iitaka-dimension
or nonvanishing hypothesis is introduced by this representation.

These are mathematical explanations, not a completed Lean dictionary to the
library's sheaf/intersection definitions. Native Comparator checks the separate
Challenge/solution pair, not the FC file. The FC file therefore has two deliberate
problem holes, `category research open` tags and no external formal-proof claim.
