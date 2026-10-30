/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.StrictTransformChartsFromCompactification
public import MixedFujita.CompactifiedPrincipalizingModels
public import MixedFujita.NondegenerateStrictTransformCharts
public import MixedFujita.CoordinateHyperplaneQuotient
public import MixedFujita.CoordinateHypersurfaceRestriction
public import MixedFujita.SmoothRestrictionInduction
public import MixedFujita.SmoothRestriction
public import MixedFujita.GenericRestriction
public import MixedFujita.LemmaThreeFromRestriction
public import MixedFujita.LemmaThreeSlices
public import MixedFujita.ClosedPointRealizationFromLemmaThree

/-!
Lemma 3 (the lower semicontinuity of thresholds in families) for smooth varieties over an
algebraically closed field of characteristic zero (step 15).

Step 9 reduced Lemma 3 in the model form on the affine opens of a smooth variety to restriction to
the fibres of products and generic restriction (check 309), proved generic restriction (check 314)
and derived restriction to fibres from strict transform charts (checks 315–347), whose input comes
from Kawamata–Viehweg vanishing on a compactified principalizing model (checks 387–393). With
Kawamata–Viehweg vanishing proved (check 558), the whole chain holds:

* restriction to the fibres of products (`fibreRestrictionStatement_of_charZero`);
* Lemma 3 in the model form on affine opens (`smoothAffineLemmaThreeStatement_of_charZero`), on
  affine space (`affineLemmaThreeStatement_of_charZero`) and at a closed point
  (`idealThresholdZariskiClosed_of_charZero`);
* the closedness on closed points of the realization sets of a variety with an ample sum
  (`closedPointRealization_of_charZero`).

All of them are for the zero boundary on a smooth variety.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Statements

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- **Restriction to the fibres of products** in characteristic zero: a point of a product
V × W at which a family has threshold at most 1/M gives a point of the fibre at which the
restriction has threshold at most 1/M. -/
theorem fibreRestrictionStatement_of_charZero : FibreRestrictionStatement K :=
  fibreRestrictionStatement_of_smoothRestriction
    (smoothRestrictionStatement_of_hypersurface
      (smoothRestrictionCodim_one_of_coordinate
        (coordinateHypersurfaceRestriction_of_quotient
          (coordinateHyperplaneQuotientRestriction_of_nondegenerateCharts
            (nondegenerateStrictTransformChartStatement_of_kvSum_of_compactifiedModels
              (fun n => kawamataViehwegVanishingSNCProjective_of_charZero K n)
              compactifiedStrictTransformModelStatement_of_charZero)))))

/-- **Lemma 3 in the model form on the affine opens of a smooth variety** in characteristic zero:
the pairs of a closed point and a parameter at which a polynomial family has threshold at most
1/M are the zero set of an ideal. -/
theorem smoothAffineLemmaThreeStatement_of_charZero : SmoothAffineLemmaThreeStatement K :=
  smoothAffineLemmaThreeStatement_of_restriction (fibreRestrictionStatement_of_charZero K)
    genericRestrictionStatement_holds

/-- **Lemma 3 in the model form on affine space** in characteristic zero. -/
theorem affineLemmaThreeStatement_of_charZero : AffineLemmaThreeStatement K :=
  affineLemmaThreeStatement_of_smoothAffineLemmaThree (smoothAffineLemmaThreeStatement_of_charZero K)

end Statements

section Point

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  {n : ℕ} [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- **Lemma 3 at a closed point of a smooth variety** in characteristic zero, for the zero
boundary. -/
theorem idealThresholdZariskiClosed_of_charZero (cY : EtaleChart K Y n) (x : Y)
    (hx : IsClosed ({x} : Set Y)) :
    IdealThresholdZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) x :=
  idealThresholdZariskiClosed_of_smoothAffineLemmaThree (smoothAffineLemmaThreeStatement_of_charZero K)
    cY x hx

end Point

/-- **The realization sets of a smooth variety with an ample sum are closed on closed points**, in
characteristic zero, for the zero boundary. -/
theorem closedPointRealization_of_charZero :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y} :=
  closedPointRealization_of_smoothAffineLemmaThree
    (fun K _ _ _ => smoothAffineLemmaThreeStatement_of_charZero K)

end MixedFujita
