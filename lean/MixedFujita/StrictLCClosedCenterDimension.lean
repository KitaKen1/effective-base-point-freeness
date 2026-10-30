/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenterClosedSubscheme
public import MixedFujita.ProperClosedImmersionDimension

/-! 標準被約中心間の実閉埋め込みによるKrull次元降下。 See reports/check-257-lc-threshold-subcenter-descent.json for the verified scope. Original lc pairs with a nonzero effective divisor avoiding all old actual lc centers have an internally constructed exact positive rational threshold and a new actual lc center. Discrepancy convexity confines a new center to the prescribed closed set if a larger coefficient is lc outside it. An actual non-lc point, old-center avoidance and exterior lc imply a strict new subcenter. Canonical reduced strict subcenters have strictly smaller ordinary Krull dimension, using an internally constructed closed immersion. These are conditional criteria: the Bertini divisor and actual ambient non-lc point from restricted concentration are not yet constructed. Center normality, center classification, general KV, original L nonvanishing and full F1/F2 remain unproved. -/

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


/-- Strict inclusion in an actual old lc center lowers the ordinary Krull
dimension of the ACTUAL reduced closed subscheme. The closed immersion between
both canonical reduced subschemes is constructed internally. No center normality,
classification or intersection theorem is needed. -/
theorem strict_subcenter_reduced_subscheme_dimension_drop
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (W : Closeds X) (hlt : W < Z) (k : ℕ)
    (hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (k + 1 : ℕ)) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal W).subscheme ≤ k := by
  classical
  let IZ := Scheme.IdealSheafData.vanishingIdeal Z
  let IW := Scheme.IdealSheafData.vanishingIdeal W
  let : IsIntegral IZ.subscheme := logCanonicalCenter_reduced_subscheme_isIntegral c f d D Z hZ
  have hI : IZ ≤ IW.map (𝟙 X) := by
    rw [Scheme.IdealSheafData.map_id]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono hlt.le
  let i := Scheme.IdealSheafData.subschemeMap IW IZ (𝟙 X) hI
  have hcomp : i ≫ IZ.subschemeι = IW.subschemeι := by
    simpa only [Category.comp_id] using Scheme.IdealSheafData.subschemeMap_subschemeι IW IZ (𝟙 X) hI
  let : IsClosedImmersion (i ≫ IZ.subschemeι) := by rw [hcomp]; infer_instance
  let : IsClosedImmersion i := IsClosedImmersion.of_comp_isClosedImmersion i IZ.subschemeι
  have hproper : Set.range i ≠ Set.univ := by
    intro hsurj
    have hranges : Set.range IW.subschemeι = Set.range IZ.subschemeι := by
      rw [← hcomp]
      change Set.range (fun w => IZ.subschemeι (i w)) = _
      calc
        Set.range (fun w => IZ.subschemeι (i w)) = IZ.subschemeι '' Set.range i := Set.range_comp _ _
        _ = Set.range IZ.subschemeι := by rw [hsurj, Set.image_univ]
    have heq : (W : Set X) = (Z : Set X) := by
      simpa only [IW.range_subschemeι, IZ.range_subschemeι, IW, IZ,
        Scheme.IdealSheafData.coe_support_vanishingIdeal] using hranges
    exact hlt.ne (SetLike.coe_injective heq)
  exact properClosedImmersion_topologicalKrullDim_le_predecessor i hproper k hdim

end MixedFujita
