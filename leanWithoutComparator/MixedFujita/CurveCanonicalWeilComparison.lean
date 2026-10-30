/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CurveCanonicalSeparatingCoordinate
public import MixedFujita.CurveCoordinateDerivativePlaceOrder
public import MixedFujita.TameDifferentialCanonicalDivisor
public import MixedFujita.CurveCenteredEtaleChart
public import MixedFujita.CurveCartierSerreDuality

@[expose] public section
open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

open TauCeti
open scoped IntermediateField
attribute [local instance 2000] Scheme.functionFieldBaseAlgebra Scheme.stalkBaseAlgebra

variable [CharZero K] [IsAlgClosed K] [IsLocallyNoetherian X]

section RatFuncExtension
variable [Algebra (RatFunc K) X.functionField]
  [IsScalarTower K (RatFunc K) X.functionField]
  [FiniteDimensional (RatFunc K) X.functionField]
  [Algebra.IsSeparable (RatFunc K) X.functionField]

theorem curveCanonicalEquation_order_eq_cotraceCoefficient
    (hF : IsFunctionField K X.functionField) (hk : IsIntegrallyClosedIn K X.functionField)
    (c₀ c : EtaleChart K X 1)
    (hcoord : algebraMap (RatFunc K) X.functionField RatFunc.X =
      etaleChartFunctionFieldCoords c₀ (MvPolynomial.X 0))
    (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hc : ¬ IsUnit (etaleChartStalkCoords c (x : X) hx (MvPolynomial.X 0))) :
    X.ord (etaleChartCanonicalEquation c₀ c : X.functionField) (x : X) =
      (ratFuncCotraceCanonicalDivisor hF hk).coeff (X.toPlace (k := K) (x : X)) := by
  let P := X.toPlace (k := K) (x : X)
  let f := etaleChartFunctionFieldCoords c₀ (MvPolynomial.X 0)
  have he : 0 < (P.ramificationIdx (RatFunc K) : ℤ) := by
    exact_mod_cast P.ramificationIdx_pos (RatFunc K)
  have heq : (etaleChartCanonicalEquation c₀ c : X.functionField) =
      etaleChartFieldCoordinateDerivative c f :=
    curveEtaleChartCanonicalEquation_eq_coordinateDerivative c₀ c
  rw [heq, ← CodimensionOnePoint.toPlace_ord (k := K) x]
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible_X_sub_C
    ((P.restrict K (RatFunc K)).degree_eq_one_of_isAlgClosed_of_isFunctionField
      (IsFunctionField.ratFunc K)) with hinf | ⟨a, ha⟩
  · obtain ⟨hord, hcoeff⟩ :=
      ratFuncCotraceCanonicalDivisor_coeff_at_infty hF hk P hinf
    rw [hcoord] at hord
    have hneg : P.ord f < 0 := by dsimp [f]; omega
    have hder : P.ord (etaleChartFieldCoordinateDerivative c f) = P.ord f - 1 :=
      (curve_coordinate_derivative_negative_place_order c x hx hc f hneg).1
    change P.ord (etaleChartFieldCoordinateDerivative c f) = _
    rw [hder, hcoeff]
    change P.ord f = _ at hord
    omega
  · obtain ⟨hord, hcoeff⟩ :=
      ratFuncCotraceCanonicalDivisor_coeff_at_finite hF hk P a ha
    have hmap : algebraMap (RatFunc K) X.functionField
        (RatFunc.X - algebraMap K (RatFunc K) a) =
        f - algebraMap K X.functionField a := by
      rw [map_sub, hcoord, ← IsScalarTower.algebraMap_apply K (RatFunc K) X.functionField]
    rw [hmap] at hord
    have hpos : 0 < P.ord (f - algebraMap K X.functionField a) := by omega
    have hder := (curve_coordinate_derivative_positive_place_order c x hx hc
      (f - algebraMap K X.functionField a) hpos).1
    rw [etaleChartFieldCoordinateDerivative_sub_baseConstant] at hder
    change P.ord (etaleChartFieldCoordinateDerivative c f) = _
    rw [hder, hcoeff, hord]

end RatFuncExtension
 
section GlobalComparison
variable [IsNoetherian X] [X.IsSeparated]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

omit [IsLocallyNoetherian X] in
/-- The original chart canonical divisor represents the intrinsic Weil canonical class. -/
theorem smoothCurveCanonicalDivisor_canonicalClass
    (hex : ValuativeCriterion.Existence (X ↘ Spec (CommRingCat.of K)))
    (hdim : ∀ x : X, coheight x ≤ 1)
    (hF : IsFunctionField K X.functionField) (hk : IsIntegrallyClosedIn K X.functionField)
    (hX : topologicalKrullDim X = 1) (c₀ : EtaleChart K X 1) :
    (Place.orderSystem hF).divisorClass
      (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim
        (smoothCanonicalDivisor c₀).toWeilDivisor) = canonicalClass hF hk := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 1 _
  let t := etaleChartFunctionFieldCoords c₀ (MvPolynomial.X 0)
  have ht : Transcendental K t := curveEtaleChart_coordinate_transcendental_schemeBase c₀
  let := hF.finiteDimensional_adjoin ht
  let : Algebra.IsSeparable K⟮t⟯ X.functionField := inferInstance
  letI := ratFuncAlgebraOfTranscendental ht
  let := isScalarTower_ratFuncAlgebraOfTranscendental ht
  let := isFunctionField_iff_functionField.mp hF
  let := isSeparable_ratFuncAlgebraOfTranscendental ht
  have hcoord : algebraMap (RatFunc K) X.functionField RatFunc.X =
      etaleChartFunctionFieldCoords c₀ (MvPolynomial.X 0) :=
    algebraMap_ratFuncAlgebraOfTranscendental_X ht
  have hW : SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim
      (smoothCanonicalDivisor c₀).toWeilDivisor = ratFuncCotraceCanonicalDivisor hF hk := by
    apply Finsupp.ext
    intro P
    obtain ⟨x, rfl⟩ := (CodimensionOnePoint.equivPlace (k := K) hex hdim).surjective P
    rw [CodimensionOnePoint.equivPlace_apply]
    change WeilDivisor.coeff _ _ = WeilDivisor.coeff _ _
    rw [SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_toPlace,
      CartierDivisor.coeff_toWeilDivisor]
    obtain ⟨c, hx, hc⟩ := smoothCurve_closedPoint_exists_centeredEtaleChart (K := K) hX
      (x : X) (TauCeti.isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one
        hdim x.property)
    exact (cartier_orderAt_eq_scheme_ord_of_localEquation _ x _
      (canonicalDivisor_isLocalEquationAt c₀ etaleCharts_cover c hx)).trans
        (curveCanonicalEquation_order_eq_cotraceCoefficient hF hk c₀ c hcoord x hx hc)
  rw [hW]
  exact ratFuncCotraceCanonicalDivisor_class hF hk

end GlobalComparison
end MixedFujita