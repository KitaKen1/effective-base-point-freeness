/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCLogCanonicalCenterCover
public import MixedFujita.SNCRationalKltThreshold

/-! 元の全モデルlc述語と実共同SNC係数判定の同値。 See reports/check-257-lc-threshold-subcenter-descent.json for the verified scope. Original lc pairs with a nonzero effective divisor avoiding all old actual lc centers have an internally constructed exact positive rational threshold and a new actual lc center. Discrepancy convexity confines a new center to the prescribed closed set if a larger coefficient is lc outside it. An actual non-lc point, old-center avoidance and exterior lc imply a strict new subcenter. Canonical reduced strict subcenters have strictly smaller ordinary Krull dimension, using an internally constructed closed immersion. These are conditional criteria: the Bertini divisor and actual ambient non-lc point from restricted concentration are not yet constructed. Center normality, center classification, general KV, original L nonvanishing and full F1/F2 remain unproved. -/

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


/-- The ORIGINAL all-model lc predicate for any rational fixed perturbation
is exactly the non-strict coefficient test on one ACTUAL joint SNC model. -/
theorem logPairIsLogCanonical_rational_perturbation_iff_snc_coefficients
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hGsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ G) (t : T) = 0)
    (p q : ℕ) (hq : 1 ≤ q) :
    LogPairIsLogCanonical c f (q * d) (q • D + (d * p) • G) ↔
      ∀ i, (q : ℤ) * cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) +
        ((d * p : ℕ) : ℤ) * cartierCoefficient (cartierPullback ρ G) (ξ i) ≤
          ((q * d : ℕ) : ℤ) := by
  have hqd : 1 ≤ q * d := Nat.mul_pos (by omega) (by omega)
  have hsupport' (t : CodimensionOnePoint T) (ht : (t : T) ∉ Set.range ξ) :
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q * d)
        (q • D + (d * p) • G) cT etaleCharts_cover) (t : T) = 0 := by
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
      cartierCoefficient_nsmul, hsupport t ht, hGsupport t ht, mul_zero, mul_zero, add_zero]
  have h := logPairIsLogCanonical_iff_crepant_snc_coefficients ρ hρ c f (q * d) hqd
    (q • D + (d * p) • G) cT ξ hinj hξ hsnc hsupport'
  simpa only [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
    cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul] using h

end MixedFujita
