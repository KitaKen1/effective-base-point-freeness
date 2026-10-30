/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateBlowupDifferential
public import MixedFujita.CartierSectionPowers

/-! Actual relative canonical divisors for coordinate-center equations.
The local determinant has exponent equal to the number of non-pivot normal
coordinates. A supplied covering by such matched charts identifies the global
divisor with that multiple of the exceptional Cartier divisor. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

universe u
variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {n : ℕ}
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem coordinateBlowup_chartRelativeJacobianDet (t : T)
    (c : EtaleChart K X n) (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U)
    (s : Finset (Fin n)) (k : Fin n)
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ t
      (etaleChartStalkCoords c (ρ t) hc (MvPolynomial.X i)) =
        if i = k then etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
        else if i ∈ s then etaleChartStalkCoords c' t hc' (MvPolynomial.X i) *
          etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
        else etaleChartStalkCoords c' t hc' (MvPolynomial.X i)) :
    chartRelativeJacobianDet ρ c c' =
      (etaleChartFunctionFieldCoords c' (MvPolynomial.X k)) ^ (s.erase k).card := by
  rw [chartRelativeJacobianDet_eq_stalk ρ t c hc c' hc',
    coordinateBlowup_etaleRelativeJacobian_det _ _ _ _ s k hcoord, map_pow]
  apply congrArg (fun a : T.functionField => a ^ (s.erase k).card)
  exact AlgHom.congr_fun (etaleChart_stalkFunctionField_comp_stalkCoords c' t hc') _

theorem coordinateBlowup_relativeCanonical_isLocalEquationAt
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : T)
    (c : EtaleChart K X n) (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U)
    (s : Finset (Fin n)) (k : Fin n)
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ t
      (etaleChartStalkCoords c (ρ t) hc (MvPolynomial.X i)) =
        if i = k then etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
        else if i ∈ s then etaleChartStalkCoords c' t hc' (MvPolynomial.X i) *
          etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
        else etaleChartStalkCoords c' t hc' (MvPolynomial.X i)) :
    (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR).IsLocalEquationAt t
      ((etaleChartCoordinateRationalUnit c' k) ^ (s.erase k).card) := by
  have h := relativeCanonicalDivisor_isLocalEquationAt ρ c₀ hX c'₀ hT hR t c hc c' hc'
  convert h using 1
  apply Units.ext
  rw [IsUnit.unit_spec, Units.val_pow_eq_pow_val]
  exact (coordinateBlowup_chartRelativeJacobianDet ρ t c hc c' hc' s k hcoord).symm

variable [IsLocallyNoetherian T] [LocallyOfFiniteType (T ↘ Spec (.of K))]

theorem coordinateBlowup_relativeCanonical_coefficient
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (c' : EtaleChart K T n) (hc' : (t : T) ∈ c'.U) (s : Finset (Fin n)) (k : Fin n)
    (hk : ¬ IsUnit (T.presheaf.germ c'.U (t : T) hc' (c'.coords (MvPolynomial.X k))))
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ (t : T)
      (etaleChartStalkCoords c (ρ (t : T)) hc (MvPolynomial.X i)) =
        if i = k then etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X k)
        else if i ∈ s then etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X i) *
          etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X k)
        else etaleChartStalkCoords c' (t : T) hc' (MvPolynomial.X i)) :
    cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR) (t : T) = ((s.erase k).card : ℤ) := by
  rw [cartierCoefficient_eq_ord (coordinateBlowup_relativeCanonical_isLocalEquationAt ρ
    c₀ hX c'₀ hT hR (t : T) c hc c' hc' s k hcoord), Units.val_pow_eq_pow_val]
  have h := etaleChart_coordinate_prod_pow_ord c' t hc' k hk (Pi.single k (s.erase k).card)
  simpa [etaleChartFunctionFieldCoords_X, Pi.single_apply] using h


omit [IsLocallyNoetherian T] [LocallyOfFiniteType (T ↘ Spec (.of K))] in
theorem coordinateBlowup_relativeCanonical_eq_nsmul
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (E : CartierDivisor T) (r : ℕ)
    (hcharts : ∀ t : T, ∃ (c : EtaleChart K X n) (hc : ρ t ∈ c.U)
      (c' : EtaleChart K T n) (hc' : t ∈ c'.U) (s : Finset (Fin n)) (k : Fin n),
      (s.erase k).card = r ∧
      E.IsLocalEquationAt t (etaleChartCoordinateRationalUnit c' k) ∧
      ∀ i, schemeStalkMapAlgHom (K := K) ρ t
        (etaleChartStalkCoords c (ρ t) hc (MvPolynomial.X i)) =
          if i = k then etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
          else if i ∈ s then etaleChartStalkCoords c' t hc' (MvPolynomial.X i) *
            etaleChartStalkCoords c' t hc' (MvPolynomial.X k)
          else etaleChartStalkCoords c' t hc' (MvPolynomial.X i)) :
    relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR = r • E := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  obtain ⟨c, hc, c', hc', s, k, hr, hE, hcoord⟩ := hcharts t
  refine ⟨(etaleChartCoordinateRationalUnit c' k) ^ r, ?_,
    cartierLocalEquation_pow E t _ hE r⟩
  simpa only [hr] using coordinateBlowup_relativeCanonical_isLocalEquationAt ρ c₀ hX c'₀ hT hR
    t c hc c' hc' s k hcoord

end MixedFujita
