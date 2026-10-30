/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CurveCoordinateDerivativeOrder
public import MixedFujita.BirationalLogPairDescent
public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler

@[expose] public section

open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
open KaehlerDifferential

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] functionFieldBaseAlgebra

theorem curveEtaleChart_coordinate_transcendental [CharZero K] (c : EtaleChart K X 1) :
    Transcendental K (etaleChartFunctionFieldCoords c (MvPolynomial.X 0)) := by
  intro halg
  have hD : D K X.functionField (etaleChartFunctionFieldCoords c (MvPolynomial.X 0)) = 0 :=
    TauCeti.D_eq_zero_of_isSeparable
      (PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral))
  have hne := (etaleChartBasis c).ne_zero 0
  rw [etaleChartBasis, etaleCoordinateBasis_apply] at hne
  exact hne hD

theorem etaleChartFieldCoordinateDerivative_sub_baseConstant_original
    (c : EtaleChart K X 1) (f : X.functionField) (a : K) :
    etaleChartFieldCoordinateDerivative c (f - algebraMap K X.functionField a) =
      etaleChartFieldCoordinateDerivative c f := by
  unfold etaleChartFieldCoordinateDerivative
  rw [Derivation.map_sub, Derivation.map_algebraMap, sub_zero]

section SchemeBase
attribute [local instance 2000] Scheme.functionFieldBaseAlgebra

theorem curveEtaleChart_coordinate_transcendental_schemeBase [CharZero K]
    (c : EtaleChart K X 1) :
    Transcendental K (etaleChartFunctionFieldCoords c (MvPolynomial.X 0)) := by
  have h := curveEtaleChart_coordinate_transcendental c
  rw [← functionFieldBaseAlgebra_eq_scheme (K := K) (X := X)]
  exact h

theorem etaleChartFieldCoordinateDerivative_sub_baseConstant
    (c : EtaleChart K X 1) (f : X.functionField) (a : K) :
    etaleChartFieldCoordinateDerivative c (f - algebraMap K X.functionField a) =
      etaleChartFieldCoordinateDerivative c f := by
  rw [← functionFieldBaseAlgebra_eq_scheme (K := K) (X := X)]
  exact etaleChartFieldCoordinateDerivative_sub_baseConstant_original c f a

end SchemeBase

end MixedFujita
