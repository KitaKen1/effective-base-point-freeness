/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FiniteSNCThresholdArithmetic
public import MixedFujita.FixedDivisorSmallKltPerturbations
public import MixedFujita.NormalEffectiveCartierPrime

/-!
On one actual joint SNC model, compute the exact rational endpoint of all-model
klt under a fixed effective Cartier perturbation. An actual prime on that model
attains discrepancy minus the denominator at the endpoint. No log-canonicity
claim at the endpoint is needed for this exact klt characterization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- All-model klt for a rational fixed-divisor perturbation is exactly the
finite coefficient condition on one actual joint SNC model. -/
theorem logPairIsKlt_rational_perturbation_iff_snc_coefficients
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (p q : ℕ) (hq : 1 ≤ q) :
    LogPairIsKlt c f (q * d) (q • D + (d * p) • G) ↔
      ∀ i, (q : ℤ) * cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) +
        ((d * p : ℕ) : ℤ) * cartierCoefficient (cartierPullback ρ G) (ξ i) <
          ((q * d : ℕ) : ℤ) := by
  have hqd : 1 ≤ q * d := Nat.mul_pos (by omega) (by omega)
  have hsupport' (t : CodimensionOnePoint T) (ht : (t : T) ∉ Set.range ξ) :
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q * d)
        (q • D + (d * p) • G) cT etaleCharts_cover) (t : T) = 0 := by
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
      cartierCoefficient_nsmul, hsupport t ht, hGsupport t ht, mul_zero, mul_zero, add_zero]
  have h := logPairIsKlt_iff_crepant_snc_coefficients ρ hρ c f (q * d) hqd
    (q • D + (d * p) • G) cT ξ hinj hξ hsnc hsupport'
  simpa only [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
    cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul] using h

/-- The minimum coefficient ratio exactly determines every rational klt
perturbation, and an actual prime attains the excluded endpoint. -/
theorem exists_snc_rational_klt_perturbation_threshold
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (hG : G.IsEffective)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (hpos : ∃ i, 0 < cartierCoefficient (cartierPullback ρ G) (ξ i)) :
    ∃ (a q₀ : ℕ) (i₀ : Fin r), 1 ≤ a ∧ 1 ≤ q₀ ∧
      0 < cartierCoefficient (cartierPullback ρ G) (ξ i₀) ∧
      (a : ℚ) / q₀ =
        ((d : ℚ) - cartierCoefficient
          (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i₀)) /
          ((d : ℚ) * cartierCoefficient (cartierPullback ρ G) (ξ i₀)) ∧
      cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q₀ * d)
        (q₀ • D + (d * a) • G) cT etaleCharts_cover) (ξ i₀) = -((q₀ * d : ℕ) : ℤ) ∧
      ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKlt c f (q * d) (q • D + (d * p) • G) ↔ (p : ℚ) / q < (a : ℚ) / q₀) := by
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  obtain ⟨a, q₀, i₀, ha, hq₀, hgi, hratio, hendpoint, htest⟩ :=
    finite_integer_coefficients_exact_threshold
      (fun i => cartierCoefficient B (ξ i))
      (fun i => cartierCoefficient (cartierPullback ρ G) (ξ i)) d hd
      (fun i => logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d D hklt cT ⟨ξ i, hξ i⟩)
      (fun i => cartierCoefficient_nonneg_of_isEffective _
        (cartierPullback_effective_of_effective ρ G hG) (ξ i)) hpos
  refine ⟨a, q₀, i₀, ha, hq₀, hgi, hratio, ?_, ?_⟩
  · have hB : cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q₀ * d)
        (q₀ • D + (d * a) • G) cT etaleCharts_cover) (ξ i₀) = ((q₀ * d : ℕ) : ℤ) := by
      rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
        cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
        cartierCoefficient_nsmul]
      exact hendpoint
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg] at hB
    omega
  · intro p q hq
    exact (logPairIsKlt_rational_perturbation_iff_snc_coefficients ρ hρ c f d hd
      D G cT ξ hinj hξ hsnc hsupport hGsupport p q hq).trans (htest p q hq)

end MixedFujita
