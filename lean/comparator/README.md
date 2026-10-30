# Comparator checks

`comparator.json` compares these declarations in `Challenge` and `FCSolution`:

- `EffectiveFreenessPublication.kollar`
- `EffectiveFreenessPublication.variants.numerical`

The main declaration is the complex projective, integer `a ≥ 1` restriction of
Kollár's linear prediction. The variant contains both the all-multiples numerical
bound and the numerical-zero principal-divisor conclusion.

The pinned native Comparator checks theorem types, definition dependencies,
permitted axioms and a fresh kernel replay of the exported solution. The only
permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.

`check-inputs.py` checks exact reference/solution signatures, source hashes, the
two identical proof copies, pins and separation of the reference imports from
the final proof. The shared solution sources have no proof holes or custom axioms.

## Linux

With bubblewrap installed:

```sh
lake exe cache get
lake comparator
```

## Local macOS

```sh
lake build Challenge FCSolution FCAudit
python3 comparator/export-local.py Challenge
python3 comparator/export-local.py FCSolution
lake comparator --inadvisably-no-sandbox \
  --challenge-from-export .lake/exports/challenge-comparator.ndjson \
  --solution-from-export .lake/exports/solution-comparator.ndjson
```

The macOS command explicitly disables the Linux-only sandbox. It is not a
sandboxed Linux CI result. The receipt binds export hashes to the source snapshot.
No older combined-package result is transferred to these new target names.

## FC statement

`check-fclike.py` checks the canonical short-header file, temporarily replaces
only its header for a strict FC audit, and checks Mathlib-only elaboration.
It restores the canonical source and returns nonzero when that source fails.
This is a statement/style check; it does not prove a dictionary between the FC
file and the proof library. See `TARGET-CORRESPONDENCE.md`.
