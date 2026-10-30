/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCCenterEffectiveAvoidance
public import MixedFujita.CartierSectionPullbackAvoidance

/-! 極小中心と中心外lcから全モデルの旧臨界摂動係数0。 See reports/check-258-minimal-lc-section-adjoint-descent.json for the verified scope. Inclusion-minimality and exterior LC force zero perturbation at every old critical prime, removing the all-old-center avoidance premise. Nonzero NATURAL restriction is equivalent to noncontainment in the actual zero-divisor support. The same threshold-prime strict old discrepancy places its center inside the original minimal center. An exact positive rational threshold and a lower-dimensional inclusion-minimal integral new-pair lc center are constructed internally. Actual original ample-adjoint sections preserve all-large ORIGINAL L ample adjoints. Exterior LC and an actual ambient non-LC point remain explicit hypotheses. Their construction from restricted concentration, appropriate center vanishing, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Exterior lc and avoidance of an inclusion-minimal actual lc center force
zero perturbation coefficient at every old critical prime of EVERY actual
proper smooth birational model. A finite classification of all centers and
normality of the center are unnecessary. -/
theorem minimal_lc_center_exterior_lc_forces_critical_pullback_coefficient_zero
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (M : CartierDivisor X) (hM : M.IsEffective)
    (j : ℕ) (Z : Closeds X)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (hZnot : ¬ Z ≤ (effectiveCartierIdealSheaf M hM).support)
    (houtside : ∀ x : X, x ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M))
    (cT : EtaleChart K T n) (t : T) (ht : Order.coheight t = 1)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) t = d) :
    cartierCoefficient (cartierPullback ρ M) t = 0 := by
  classical
  have hn := cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ M hM) t
  by_contra hne
  have hp : 0 < cartierCoefficient (cartierPullback ρ M) t := by omega
  let C : Closeds X := ⟨closure ({ρ t} : Set X), isClosed_closure⟩
  have hC : LogPairIsLogCanonicalCenter c f d D C :=
    crepant_critical_prime_is_logCanonicalCenter ρ hρ c f d D hlc cT t ht hcrit
  have hCM : C ≤ (effectiveCartierIdealSheaf M hM).support :=
    positive_effective_pullback_prime_center_le_source_support ρ M hM t hp
  have hCdis : cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t = -(d : ℤ) := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg] at hcrit
    omega
  have hCZ : C ≤ Z := by
    intro x hxC
    by_contra hxZ
    have hxcl : x ∈ closure ({(ρ ≫ 𝟙 X) t} : Set X) := by
      change x ∈ closure ({ρ t} : Set X) at hxC
      simpa only [Category.comp_id] using hxC
    have hlarge := houtside x hxZ T ρ hρ cT t ht hxcl
    rw [logDiscrepancyDivisor_add_source, logDiscrepancyDivisor_scale_denominator,
      cartierCoefficient_sub, cartierCoefficient_nsmul, hCdis] at hlarge
    push_cast at hlarge
    nlinarith
  exact hZnot ((hmin C hC hCZ) ▸ hCM)

end MixedFujita
