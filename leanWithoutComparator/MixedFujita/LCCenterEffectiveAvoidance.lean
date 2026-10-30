/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCLogCanonicalCenterCover
public import MixedFujita.PrincipalizedIdealCoefficients

/-! 実lc中心回避から旧臨界素因子上の摂動係数0。 See reports/check-257-lc-threshold-subcenter-descent.json for the verified scope. Original lc pairs with a nonzero effective divisor avoiding all old actual lc centers have an internally constructed exact positive rational threshold and a new actual lc center. Discrepancy convexity confines a new center to the prescribed closed set if a larger coefficient is lc outside it. An actual non-lc point, old-center avoidance and exterior lc imply a strict new subcenter. Canonical reduced strict subcenters have strictly smaller ordinary Krull dimension, using an internally constructed closed immersion. These are conditional criteria: the Bertini divisor and actual ambient non-lc point from restricted concentration are not yet constructed. Center normality, center classification, general KV, original L nonvanishing and full F1/F2 remain unproved. -/

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


/-- A positive coefficient of an actual effective Cartier pullback forces its
closed center into the support of the ORIGINAL effective Cartier divisor. -/
theorem positive_effective_pullback_prime_center_le_source_support
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    (ρ : T ⟶ X) [IsDominant ρ] (G : CartierDivisor X) (hG : G.IsEffective)
    (t : T) (ht : 0 < cartierCoefficient (cartierPullback ρ G) t) :
    closure ({ρ t} : Set X) ⊆ (effectiveCartierIdealSheaf G hG).support := by
  have hpull : t ∈ ((effectiveCartierIdealSheaf G hG).comap ρ).support := by
    rw [← effectiveCartierIdealSheaf_cartierPullback ρ G hG]
    by_contra h
    have hz := cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf
      (cartierPullback ρ G) (cartierPullback_isEffective ρ G hG) t h
    omega
  rw [Scheme.IdealSheafData.support_comap] at hpull
  exact closure_minimal (Set.singleton_subset_iff.mpr hpull) (effectiveCartierIdealSheaf G hG).support.isClosed


/-- Avoidance of EVERY original actual lc center forces the pullback
perturbation coefficient to vanish at every critical prime of every test model. -/
theorem lc_center_avoidance_forces_critical_pullback_coefficient_zero
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (G : CartierDivisor X) (hG : G.IsEffective)
    (havoid : ∀ Z : Closeds X, LogPairIsLogCanonicalCenter c f d D Z →
      ¬ Z ≤ (effectiveCartierIdealSheaf G hG).support)
    (cT : EtaleChart K T n) (t : T) (ht : Order.coheight t = 1)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) t = d) :
    cartierCoefficient (cartierPullback ρ G) t = 0 := by
  have hn := cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ G hG) t
  by_contra hne
  have hp : 0 < cartierCoefficient (cartierPullback ρ G) t := by omega
  exact havoid ⟨closure ({ρ t} : Set X), isClosed_closure⟩
    (crepant_critical_prime_is_logCanonicalCenter ρ hρ c f d D hlc cT t ht hcrit)
    (positive_effective_pullback_prime_center_le_source_support ρ G hG t hp)

end MixedFujita
