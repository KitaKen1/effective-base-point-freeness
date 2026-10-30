/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCCenteredDiscrepancyBound

/-!
Non-strict discrepancy bounds for signed SNC boundaries. Only components through
the actual centre need coefficient at most the denominator. The Jacobian bound
and nonnegative coordinate orders prove the estimate on every smooth birational
test, without a properness assumption on that test.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Coefficients at most the denominator give the non-strict discrepancy bound. -/
theorem snc_integer_logCanonical_bound_of_active_coefficients {ι : Type*} [Fintype ι]
    (d : ℕ) (hd : 1 ≤ d) (J : ℤ) (hJ : 0 ≤ J) (v b : ι → ℤ)
    (hv : ∀ i, 0 ≤ v i) (hsum : ∑ i, v i ≤ 1 + J)
    (hb : ∀ i, v i ≠ 0 → b i ≤ (d : ℤ)) :
    -(d : ℤ) ≤ (d : ℤ) * J - ∑ i, b i * v i := by
  classical
  have hterm : ∑ i, b i * v i ≤ ∑ i, (d : ℤ) * v i := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : v i = 0
    · simp only [hi, mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (hb i hi) (hv i)
  rw [← Finset.mul_sum] at hterm
  have hmul := mul_le_mul_of_nonneg_left hsum (by omega : (0 : ℤ) ≤ d)
  nlinarith

/-- Only SNC members through the actual centre need coefficients at most d.
The source and test model are smooth, but the test map need not be proper. -/
theorem isSNCFamily_actual_logCanonical_bound_at_center
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient B (z : X) = 0)
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T)
    (hb : ∀ i, ρ (t : T) ∈ closure ({ξ i} : Set X) →
      cartierCoefficient B (ξ i) ≤ (d : ℤ)) :
    -(d : ℤ) ≤ cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      cT etaleCharts_cover) (t : T) := by
  obtain ⟨c, σ, hc, hcsnc, hformula⟩ := isSNCFamily_actual_discrepancy_formula
    ρ hρ c₀ f₀ d B ξ hinj hξ hsnc hsupport cT t
  obtain ⟨c', hc'⟩ : ∃ c' : EtaleChart K T n, (t : T) ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸
      Opens.mem_top (t : T))
  rw [hformula c' hc']
  have hJ : 0 ≤ T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
    rw [chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc']
    exact scheme_ord_nonneg_of_mem_stalk (t : T) _ ⟨_, rfl⟩
  apply snc_integer_logCanonical_bound_of_active_coefficients d hd _ hJ
    (fun i => T.ord ((dominantFunctionFieldMap ρ).hom
      (sncChartComponentEquation c σ i : X.functionField)) (t : T))
    (fun i => cartierCoefficient B (ξ i))
    (fun i => sncChartComponentEquation_pullback_ord_nonneg ρ c σ (t : T) hc i)
    (actual_snc_coordinate_sum_le_jacobian ρ hρ t c hc ξ σ hcsnc c' hc')
  intro i hi
  apply hb i
  by_contra hnot
  exact hi (sncChartComponentEquation_pullback_ord_eq_zero_of_notMem_closure
    ρ c ξ σ hcsnc (t : T) hc i hnot)

end MixedFujita
