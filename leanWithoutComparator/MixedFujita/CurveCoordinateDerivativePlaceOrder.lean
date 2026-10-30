/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CurveCoordinateDerivativeOrder

/-! Coordinate differentiation lowers every nonzero zero or pole order by one
in characteristic zero, at an actual centered etale curve chart. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

section SchemePlaces
open TauCeti
attribute [local instance 2000] Scheme.functionFieldBaseAlgebra Scheme.stalkBaseAlgebra

theorem curve_coordinate_derivative_positive_place_order [CharZero K] [IsLocallyNoetherian X]
    (c : EtaleChart K X 1) (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hc : ¬ IsUnit (etaleChartStalkCoords c (x : X) hx (MvPolynomial.X 0)))
    (f : X.functionField) (hf : 0 < (X.toPlace (k := K) (x : X)).ord f) :
    (X.toPlace (k := K) (x : X)).ord
        (etaleChartFieldCoordinateDerivative c f) =
        (X.toPlace (k := K) (x : X)).ord f - 1 ∧
      etaleChartFieldCoordinateDerivative c f ≠ 0 := by
  let P := X.toPlace (k := K) (x : X)
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨r, hr⟩ := (X.mem_toPlace_integers_iff_exists_stalk (k := K) (x : X) f).mp
    ((P.mem_integers_iff_ord_nonneg).mpr hf.le)
  have hr0 : r ≠ 0 := by intro h; apply hf0; rw [← hr, h, map_zero]
  have hru : ¬ IsUnit r := by
    intro hu
    have hunit := hu.map (X.stalkToPlaceIntegersAlgEquiv (k := K) (x : X)).toRingHom
    have hne : ((X.stalkToPlaceIntegersAlgEquiv (k := K) (x : X) r : P.integers) :
        X.functionField) ≠ 0 := by
      rw [Scheme.coe_stalkToPlaceIntegersAlgEquiv, hr]
      exact hf0
    have ho := (P.isUnit_iff_ord_eq_zero hne).mp hunit
    rw [Scheme.coe_stalkToPlaceIntegersAlgEquiv, hr] at ho
    exact (ne_of_gt hf) ho
  have h := curve_stalk_coordinate_derivative_exact_order c x hx hc r hr0 hru
  rw [hr] at h
  simpa only [CodimensionOnePoint.toPlace_ord, etaleChartFieldCoordinateDerivative] using h


theorem curve_coordinate_derivative_negative_place_order [CharZero K] [IsLocallyNoetherian X]
    (c : EtaleChart K X 1) (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hc : ¬ IsUnit (etaleChartStalkCoords c (x : X) hx (MvPolynomial.X 0)))
    (f : X.functionField) (hf : (X.toPlace (k := K) (x : X)).ord f < 0) :
    (X.toPlace (k := K) (x : X)).ord
        (etaleChartFieldCoordinateDerivative c f) =
        (X.toPlace (k := K) (x : X)).ord f - 1 ∧
      etaleChartFieldCoordinateDerivative c f ≠ 0 := by
  let P := X.toPlace (k := K) (x : X)
  let δ := etaleChartFieldCoordinateDerivative c
  have hf0 : f ≠ 0 := by rintro rfl; simp at hf
  obtain ⟨hi, hi0⟩ := curve_coordinate_derivative_positive_place_order c x hx hc f⁻¹
    (by rw [Place.ord_inv]; exact neg_pos.mpr hf)
  have heq := etaleChartFieldCoordinateDerivative_eq_neg_sq_mul_inv c f hf0
  have hdf0 : δ f ≠ 0 := by
    change etaleChartFieldCoordinateDerivative c f ≠ 0
    rw [heq]
    exact mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ hf0)) hi0
  refine ⟨?_, hdf0⟩
  change P.ord (etaleChartFieldCoordinateDerivative c f) = P.ord f - 1
  rw [heq, P.ord_mul (neg_ne_zero.mpr (pow_ne_zero _ hf0)) hi0, P.ord_neg, P.ord_pow,
    hi, P.ord_inv]
  ring

end SchemePlaces

end MixedFujita
