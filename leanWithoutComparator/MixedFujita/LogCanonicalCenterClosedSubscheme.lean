/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenters
public import MixedFujita.RadicalIdealSubschemeReduced

/-! 実lc中心の標準非klt台への配置と被約閉部分の整性。 See reports/check-255-minimal-valuative-lc-center.json for the verified scope. Actual lc centers carry a proper smooth birational prime of discrepancy exactly -d. Original non-klt points are exactly points in such centers. Mathlib Noetherian closed-set well-foundedness supplies inclusion-minimal centers without classifying all SNC strata or all centers first. One actual SNC model gives a finite center cover of the whole non-klt locus, not a list of all lc centers. Reduced center subschemes are integral. Original positive-numerical normal klt BPF data construct an inclusion-minimal actual lc center, its integral reduced subscheme and strict geometric dimension bound without an initial L section or KV. Center normality, intersections/uniqueness, appropriate center vanishing and restriction lifting/nonvanishing, nu=0, initial L nonvanishing, exterior control/dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower


/-- Every actual lc center lies in a closed set which represents the original
all-model non-klt locus. This connects valuative centers to the canonical ideal. -/
theorem logCanonicalCenter_le_nonKlt_support
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (I : X.IdealSheafData)
    (hI : ∀ x : X, x ∈ (I.support : Set X) ↔ ¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z) : Z ≤ I.support := by
  intro x hx
  exact (hI x).mpr (logPairIsLogCanonicalCenter_not_kltOverBasePoint c f d D Z hZ x hx)


/-- The reduced closed subscheme of any genuine lc center is INTEGRAL.
This asserts reducedness and irreducibility; it does not assert normality. -/
theorem logCanonicalCenter_reduced_subscheme_isIntegral
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  have hsupport : (J.support : Set X) = Z := by
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hred : IsReduced J.subscheme :=
    idealSheaf_subscheme_isReduced_of_affine_radical J (fun U => PrimeSpectrum.isRadical_vanishingIdeal _)
  have hrange : IsIrreducible (Set.range J.subschemeι) := by
    rw [J.range_subschemeι, hsupport]
    exact logPairIsLogCanonicalCenter_isIrreducible c f d D Z hZ
  have hirr : IrreducibleSpace J.subscheme := by
    exact J.subschemeι.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
      (isIrreducible_iff_irreducibleSpace.mp hrange)
  exact (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨hirr, hred⟩

end MixedFujita
