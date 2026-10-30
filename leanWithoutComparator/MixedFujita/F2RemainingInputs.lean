/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.KltClosedPointMinimizer
public import MixedFujita.AmbroStrictDimensionReduction
public import MixedFujita.NefAddAmpleProof

/-!
The remaining inputs of K-NF and F2 after the proof of Kawamata–Viehweg vanishing (steps 15–17).

K-NF follows from Kawamata–Viehweg vanishing and the closedness of the realization sets of klt
pairs (check 94); with KV proved (check 558) only the closedness remains
(`KltRealizationClosedness`, `kawamataNumericalFreeness_of_kltRealizationClosedness`). It holds for
klt pairs with effective boundary on smooth varieties (checks 560, 561). F2 follows from K-NF, the
base point free theorem for klt pairs and Ambro's canonical bundle formula for contractions to
lower-dimensional bases ("nef plus ample is ample" is proved), so
F2 ⇐ `KltRealizationClosedness` + `KltBasePointFreeStatement` + `AmbroStrictDimensionStatement`
(`linearEffectiveFreeness_of_kltRealizationClosedness_of_basePointFree_of_ambro`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- The closedness of the realization sets of klt pairs, the remaining input of K-NF: for every klt
pair on an integral variety of finite type over an uncountable algebraically closed field of
characteristic zero, every ample A and every closed point x, the realization sets in the tuple at
x are Zariski closed and the realization sets in the point are closed on closed points, for all
large multiples of A. -/
def KltRealizationClosedness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
    ∀ (D₀ A : CartierDivisor Y), LogPairIsKlt cY fY d D₀ → CartierIsAmpleProj K A →
    ∀ x : Y, IsClosed ({x} : Set Y) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d
          D₀ (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})

/-- **K-NF from the closedness of the realization sets of klt pairs** (Kawamata–Viehweg vanishing
is proved). -/
theorem kawamataNumericalFreeness_of_kltRealizationClosedness
    (h : KltRealizationClosedness.{u}) : KawamataNumericalFreeness.{u} :=
  kawamataNumericalFreeness_of_kv_of_closedPointRealization
    (fun K _ _ _ n => kawamataViehwegVanishingSNC_of_charZero K n) h

/-- **F2 from the closedness of the realization sets of klt pairs, the base point free theorem for
klt pairs and Ambro's canonical bundle formula for contractions to lower-dimensional bases.** -/
theorem linearEffectiveFreeness_of_kltRealizationClosedness_of_basePointFree_of_ambro
    (h : KltRealizationClosedness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hamb : AmbroStrictDimensionStatement.{u}) : LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_knf_of_bpf_of_nefAddAmple_of_strictAmbro
    (kawamataNumericalFreeness_of_kltRealizationClosedness h) hbpf nefAddAmpleStatement_holds hamb

end MixedFujita
