/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCAppendedCoordinateJacobianBound
public import MixedFujita.SNCLogCanonicalDiscrepancyBound

/-!
At the actual centre of any smooth birational test, an adapted transverse
Cartier coordinate gives the coefficient-one lc discrepancy bound. The map
of the test need not be proper, and the old boundary may have negative
coefficients. Its local product and the full Jacobian bound are internal.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A coefficient-one extra cut uses precisely its remaining share of the Jacobian sum. -/
theorem snc_integer_logCanonical_bound_with_added_coefficient_one {ι : Type*} [Fintype ι]
    (d : ℕ) (J w : ℤ) (v b : ι → ℤ) (hv : ∀ i, 0 ≤ v i)
    (hsum : ∑ i, v i + w ≤ 1 + J) (hb : ∀ i, v i ≠ 0 → b i ≤ (d : ℤ)) :
    -(d : ℤ) ≤ (d : ℤ) * J - ∑ i, b i * v i - (d : ℤ) * w := by
  classical
  have hterm : ∑ i, b i * v i ≤ (d : ℤ) * ∑ i, v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : v i = 0
    · simp only [hi, mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hb i hi) (hv i)
  have hmul := mul_le_mul_of_nonneg_left hsum (Int.natCast_nonneg d)
  nlinarith

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- A local adapted Cartier chart internally bounds every actual birational test discrepancy. -/
theorem isSNCChartWith_actual_logCanonical_bound_with_cut_at_center
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (B G : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient B (z : X) = 0)
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T)
    (hb : ∀ i, ρ (t : T) ∈ closure ({ξ i} : Set X) → cartierCoefficient B (ξ i) ≤ (d : ℤ))
    (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (Z : Set X) (j : Fin n)
    (hc : ρ (t : T) ∈ c.U) (hchart : IsSNCChartWith c ξ σ Z (some j))
    (hG : G.IsLocalEquationAt (ρ (t : T)) (etaleChartCoordinateRationalUnit c j)) :
    -(d : ℤ) ≤ cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + (B + d • G))
      cT etaleCharts_cover) (t : T) := by
  letI : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : ∀ z : CodimensionOnePoint X, IsRegularLocalRing (X.presheaf.stalk (z : X)) :=
    fun z => isSNCFamily_stalk_regular hsnc (z : X)
  have : ∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    fun z => inferInstance
  obtain ⟨fB, hfB, uB, hprod⟩ := normal_isSNCChart_boundary_local_product
    (isSNCFamily_stalk_isIntegrallyClosed hsnc) B c ξ hinj hξ σ hchart.1 hsupport (ρ (t : T)) hc
  have hB := cartierPullback_coefficient_of_local_product ρ B t fB hfB uB _ _ hprod
  obtain ⟨c', hc'⟩ : ∃ c' : EtaleChart K T n, (t : T) ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top (t : T))
  have hrelative : cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀
      etaleCharts_cover cT etaleCharts_cover) (t : T) =
      T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
    have hloc := relativeCanonicalDivisor_isLocalEquationAt ρ c₀ etaleCharts_cover cT
      etaleCharts_cover (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ cT)
      (t : T) c hc c' hc'
    unfold birationalRelativeCanonicalDivisor
    rw [cartierCoefficient_eq_ord hloc, IsUnit.unit_spec]
  have hGcoef : cartierCoefficient (cartierPullback ρ G) (t : T) =
      T.ord ((dominantFunctionFieldMap ρ).hom
        (etaleChartCoordinateRationalUnit c j : X.functionField)) (t : T) := by
    rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ G (t : T) hG)]
    rfl
  rw [logDiscrepancyDivisor_boundary_add, cartierPullback_add, cartierPullback_nsmul,
    cartierCoefficient_sub, cartierCoefficient_add, cartierCoefficient_nsmul,
    cartierCoefficient_nsmul, hrelative, hB, hGcoef, sub_add_eq_sub_sub]
  apply snc_integer_logCanonical_bound_with_added_coefficient_one d _ _
    (fun i => T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) (t : T))
    (fun i => cartierCoefficient B (ξ i))
    (fun i => sncChartComponentEquation_pullback_ord_nonneg ρ c σ (t : T) hc i)
    (actual_snc_appended_coordinate_sum_le_jacobian ρ hρ t c hc ξ σ Z j hchart c' hc')
  intro i hi
  apply hb i
  by_contra hnot
  exact hi (sncChartComponentEquation_pullback_ord_eq_zero_of_notMem_closure
    ρ c ξ σ hchart.1 (t : T) hc i hnot)

end MixedFujita
