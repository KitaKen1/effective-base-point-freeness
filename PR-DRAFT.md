# Draft: effective freeness and its numerical variant

This is a local draft, not a submitted PR.

**Proposed title:** `feat(Paper): add the projective integral case of effective freeness`

Formalizes the complex projective case with an effective rational boundary and
integer `a ≥ 1` of the linear prediction after Theorem 1.1 in Kollár (1993), p.596:
if `D` is nef Cartier and `aD − (K_X + Δ)` is nef and big, then `(a+n+1)D` is
globally generated. It does not claim the original setting's full `a ≥ 0` range.

Includes a numerical-dimension variant: every `m ≥ a + ν(D) + 1` works, and
`ν(D) = 0` implies `D ∼ 0`. This is a project variant, rather than a quotation of
the full formula from Kollár or OpenAI. The external library proof derives the
restricted parent statement from the variant using `ν(D) ≤ n`.

The one-file problem statement imports only `FormalConjecturesUtil`. Its
definitions use local Cartier equations, rational sections and discrepancies.
There is no Iitaka-dimension or nonvanishing input. The separate library-backed
proof targets use only the standard three axioms. A Lean dictionary between its
representation and the standalone FC representation remains to be supplied, so
this draft has no `formal_proof` attribute or `research solved` claim.

Sources: [Kollár (1993)](https://doi.org/10.1007/BF01445123), pp.595–596;
[Fujino (2011), Theorem 2.1](https://www.math.kyoto-u.ac.jp/preprint/2011/03fujino.pdf)
for qualitative background. OpenAI's smooth Fujita manuscript informed the proof
strategy; it is not the source of this klt numerical statement.

Local build, Comparator and FC results are recorded in `verification/`. The
retained short project header is incompatible with FC's strict copyright linter;
the checker separately audits a temporary standard-header copy. No linter is
disabled. Formalization and mathematical exploration used ChatGPT and OpenAI Codex.
