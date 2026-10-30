/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GeometricSmoothTaylor
public import MixedFujita.CanonicalDivisor
public import MixedFujita.EtalePolynomialDifferentials

@[expose] public section
open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

theorem smoothCurve_closedPoint_exists_centeredEtaleChart
    (hX : topologicalKrullDim X = 1) (x : X) (hclosed : IsClosed {x}) :
    ∃ (c : EtaleChart K X 1) (hx : x ∈ c.U),
      ¬ IsUnit (etaleChartStalkCoords c x hx (MvPolynomial.X 0)) := by
  obtain ⟨U, hU, hx, β, g, hg, hc⟩ :=
    geometricSmoothScheme_closedPoint_exists_centeredAffineEtaleChart (K := K) 1 hX x hclosed
  let c : EtaleChart K X 1 := ⟨U, hU, ⟨⟨x, hx⟩⟩, g,
    ringHom_formallyEtale_of_etale _ hg⟩
  refine ⟨c, hx, ?_⟩
  have hb : β (etaleChartStalkCoords c x hx (MvPolynomial.X 0)) = 0 := by
    simpa only [etaleChartStalkCoords, AlgHom.comp_apply,
      sectionStalkAlgHom, rationalAffineGermPoint, MvPolynomial.constantCoeff_X] using
      hc (MvPolynomial.X 0)
  intro hu
  have hunit := hu.map β.toRingHom
  change IsUnit (β (etaleChartStalkCoords c x hx (MvPolynomial.X 0))) at hunit
  rw [hb] at hunit
  exact not_isUnit_zero hunit

end MixedFujita