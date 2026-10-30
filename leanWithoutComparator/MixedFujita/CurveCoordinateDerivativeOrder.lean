/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.DVRDerivationExactOrder
public import MixedFujita.CurveCanonicalDifferentialLattice
public import MixedFujita.CartierWeilVanishingOrder

/-! Exact local derivative orders and the original curve canonical equation. -/
@[expose] public section
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower functionFieldBaseAlgebra functionFieldBaseScalarTower
  canonicalStalkFunctionFieldScalarTower

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

theorem etaleChart_coordinateDerivation_map_stalk (c : EtaleChart K X 1)
    (x : X) (hx : x ∈ c.U) (r : X.presheaf.stalk x) :
    etaleCoordinateDerivation (etaleChartFunctionFieldCoords c)
        (etaleChartFunctionFieldCoords_formallyEtale c) 0
        (algebraMap (X.presheaf.stalk x) X.functionField r) =
      algebraMap (X.presheaf.stalk x) X.functionField
        (etaleCoordinateDerivation (etaleChartStalkCoords c x hx)
          (etaleChartStalkCoords_formallyEtale c x hx) 0 r) := by
  have h := etaleCoordinateDerivation_comp (stalkFunctionFieldAlgHom (K := K) x)
    (etaleChartStalkCoords c x hx) (etaleChartStalkCoords_formallyEtale c x hx)
    (formallyEtale_comp _ (stalkFunctionFieldAlgHom_formallyEtale (K := K) x)
      _ (etaleChartStalkCoords_formallyEtale c x hx)) 0 r
  simp only [etaleChart_stalkFunctionField_comp_stalkCoords c x hx] at h
  have hσ (a : X.presheaf.stalk x) : (stalkFunctionFieldAlgHom (K := K) x) a =
      algebraMap (X.presheaf.stalk x) X.functionField a := rfl
  simp only [hσ] at h
  exact h

theorem curveEtaleChartCanonicalEquation_eq_coordinateDerivative (c₀ c : EtaleChart K X 1) :
    (etaleChartCanonicalEquation c₀ c : X.functionField) =
      etaleCoordinateDerivation (etaleChartFunctionFieldCoords c)
        (etaleChartFunctionFieldCoords_formallyEtale c) 0
        (etaleChartFunctionFieldCoords c₀ (MvPolynomial.X 0)) := by
  rw [etaleChartCanonicalEquation_val, Module.Basis.det_apply, Matrix.det_fin_one,
    Module.Basis.toMatrix_apply, etaleCoordinateDerivation_apply]
  congr 2
  exact etaleCoordinateBasis_apply _ _ _

theorem curve_stalk_coordinate_derivative_exact_order [CharZero K] [IsLocallyNoetherian X]
    (c : EtaleChart K X 1) (x : CodimensionOnePoint X) (hx : (x : X) ∈ c.U)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hc : ¬ IsUnit (etaleChartStalkCoords c (x : X) hx (MvPolynomial.X 0)))
    (r : X.presheaf.stalk (x : X)) (hr : r ≠ 0) (hru : ¬ IsUnit r) :
    X.ord (etaleCoordinateDerivation (etaleChartFunctionFieldCoords c)
        (etaleChartFunctionFieldCoords_formallyEtale c) 0
        (algebraMap (X.presheaf.stalk (x : X)) X.functionField r)) (x : X) =
        X.ord (algebraMap (X.presheaf.stalk (x : X)) X.functionField r) (x : X) - 1 ∧
      etaleCoordinateDerivation (etaleChartFunctionFieldCoords c)
        (etaleChartFunctionFieldCoords_formallyEtale c) 0
        (algebraMap (X.presheaf.stalk (x : X)) X.functionField r) ≠ 0 := by
  let y := etaleChartStalkCoords c (x : X) hx
  let hy := etaleChartStalkCoords_formallyEtale c (x : X) hx
  let δ := etaleCoordinateDerivation y hy 0
  have ht := etaleDVR_coordinate_irreducible y hy 0 hc
  have hδ : δ (y (MvPolynomial.X 0)) = 1 := by
    exact etaleCoordinateDerivation_coordinate y hy 0 0
  obtain ⟨m, hm, hro, hdro, hdr⟩ :=
    dvr_derivation_exact_positive_order δ _ ht hδ r hr hru
  have hro' := scheme_ord_regular_eq_localAdicOrder_nat x r hr m
    ((dvr_localAdicOrder_eq_ringOrd r).trans hro)
  have hdro' := scheme_ord_regular_eq_localAdicOrder_nat x (δ r) hdr (m - 1)
    ((dvr_localAdicOrder_eq_ringOrd (δ r)).trans hdro)
  rw [etaleChart_coordinateDerivation_map_stalk c (x : X) hx r]
  refine ⟨?_, ?_⟩
  · change X.ord (algebraMap (X.presheaf.stalk (x : X)) X.functionField (δ r)) (x : X) = _
    rw [hdro', hro']
    omega
  · exact fun h => hdr ((IsFractionRing.injective (X.presheaf.stalk (x : X)) X.functionField)
      (h.trans (map_zero _).symm))

theorem derivation_eq_neg_sq_mul_inv_derivative
    {K F : Type*} [CommRing K] [Field F] [Algebra K F]
    (δ : Derivation K F F) (f : F) (hf : f ≠ 0) :
    δ f = -(f ^ 2) * δ f⁻¹ := by
  have hprod : f * δ f⁻¹ + f⁻¹ * δ f = 0 := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← δ.leibniz, mul_inv_cancel₀ hf, δ.map_one_eq_zero]
  have hsecond : f⁻¹ * δ f = -(f * δ f⁻¹) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hprod
  calc
    δ f = (f * f⁻¹) * δ f := by rw [mul_inv_cancel₀ hf, one_mul]
    _ = f * (f⁻¹ * δ f) := by ring
    _ = f * -(f * δ f⁻¹) := by rw [hsecond]
    _ = _ := by ring


/-- The original coordinate derivation, viewed as a function so that its value can be
compared with place orders without changing either base-algebra presentation. -/
noncomputable def etaleChartFieldCoordinateDerivative (c : EtaleChart K X 1) :
    X.functionField → X.functionField :=
  etaleCoordinateDerivation (etaleChartFunctionFieldCoords c)
    (etaleChartFunctionFieldCoords_formallyEtale c) 0

theorem etaleChartFieldCoordinateDerivative_eq_neg_sq_mul_inv
    (c : EtaleChart K X 1) (f : X.functionField) (hf : f ≠ 0) :
    etaleChartFieldCoordinateDerivative c f =
      -(f ^ 2) * etaleChartFieldCoordinateDerivative c f⁻¹ :=
  derivation_eq_neg_sq_mul_inv_derivative _ f hf

end MixedFujita
