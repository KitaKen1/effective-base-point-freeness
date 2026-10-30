/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteLCThresholdArithmetic
public import MixedFujita.LCCenterEffectiveAvoidance
public import MixedFujita.SNCRationalLCThreshold
public import MixedFujita.SignedRationalKltPerturbationThreshold

/-! 元lc対の正の厳密有理閾値と新しい実lc中心。 See reports/check-257-lc-threshold-subcenter-descent.json for the verified scope. Original lc pairs with a nonzero effective divisor avoiding all old actual lc centers have an internally constructed exact positive rational threshold and a new actual lc center. Discrepancy convexity confines a new center to the prescribed closed set if a larger coefficient is lc outside it. An actual non-lc point, old-center avoidance and exterior lc imply a strict new subcenter. Canonical reduced strict subcenters have strictly smaller ordinary Krull dimension, using an internally constructed closed immersion. These are conditional criteria: the Bertini divisor and actual ambient non-lc point from restricted concentration are not yet constructed. Center normality, center classification, general KV, original L nonvanishing and full F1/F2 remain unproved. -/

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


/-- An original signed lc pair and an effective nonzero divisor avoiding ALL
original actual lc centers have a positive exact rational LC threshold and a
NEW actual lc center contained in that divisor. The common model is internal;
the original pair need not be klt or have an effective boundary. -/
theorem exists_exact_positive_rational_lc_threshold_with_new_center
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D)
    (G : CartierDivisor X) (hG : G.IsEffective) (hne : G ≠ 0)
    (havoid : ∀ Z : Closeds X, LogPairIsLogCanonicalCenter c f d D Z →
      ¬ Z ≤ (effectiveCartierIdealSheaf G hG).support) :
    ∃ a q : ℕ, 1 ≤ a ∧ 1 ≤ q ∧ 0 < (a : ℚ) / q ∧
      LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • G) ∧
      (¬ LogPairIsKlt c f (q * d) (q • D + (d * a) • G)) ∧
      (∀ p s : ℕ, 1 ≤ s →
        (LogPairIsLogCanonical c f (s * d) (s • D + (d * p) • G) ↔ (p : ℚ) / s ≤ (a : ℚ) / q)) ∧
      ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • G) W ∧
        W ≤ (effectiveCartierIdealSheaf G hG).support ∧ ¬ LogPairIsLogCanonicalCenter c f d D W := by
  classical
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, hGsupp⟩ :=
    exists_proper_snc_model_with c f d D (fun _ : PUnit.{1} => G)
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨t, ht⟩ := proper_birational_effective_pullback_exists_positive_prime
    hnorm hnormT ρ hρ G hG hne
  have htin : (t : T) ∈ Set.range ξ := by
    by_contra h
    rw [hGsupp PUnit.unit t h] at ht
    exact lt_irrefl _ ht
  obtain ⟨i, hi⟩ := htin
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let b (i : Fin r) := cartierCoefficient B (ξ i)
  let g (i : Fin r) := cartierCoefficient (cartierPullback ρ G) (ξ i)
  have hb (i : Fin r) : b i ≤ (d : ℤ) :=
    logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hlc cT ⟨ξ i, hξ i⟩
  have hg (i : Fin r) : 0 ≤ g i :=
    cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ G hG) (ξ i)
  have hcritical (i : Fin r) (hi : b i = (d : ℤ)) : g i = 0 :=
    lc_center_avoidance_forces_critical_pullback_coefficient_zero ρ hρ c f d D hlc G hG havoid cT (ξ i) (hξ i) hi
  have hpos : ∃ i, 0 < g i := ⟨i, by simpa only [g, hi] using ht⟩
  obtain ⟨a, q, i₀, ha, hq, hgi, _, _, hendpoint, htest⟩ :=
    finite_integer_lc_coefficients_exact_threshold b g d hd hb hg hcritical hpos
  have htestLC (p s : ℕ) (hs : 1 ≤ s) :
      LogPairIsLogCanonical c f (s * d) (s • D + (d * p) • G) ↔ (p : ℚ) / s ≤ (a : ℚ) / q :=
    (logPairIsLogCanonical_rational_perturbation_iff_snc_coefficients ρ hρ c f d hd D G
      cT ξ hinj hξ hsnc hsupp (hGsupp PUnit.unit) p s hs).trans (htest p s hs)
  have hLc := (htestLC a q hq).mpr le_rfl
  have hnewcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q * d)
      (q • D + (d * a) • G) cT etaleCharts_cover) (ξ i₀) = ((q * d : ℕ) : ℤ) := by
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_nsmul]
    exact hendpoint
  let W : Closeds X := ⟨closure ({ρ (ξ i₀)} : Set X), isClosed_closure⟩
  have hW : LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • G) W :=
    crepant_critical_prime_is_logCanonicalCenter ρ hρ c f (q * d) _ hLc cT (ξ i₀) (hξ i₀) hnewcrit
  have hWG : W ≤ (effectiveCartierIdealSheaf G hG).support :=
    positive_effective_pullback_prime_center_le_source_support ρ G hG (ξ i₀) hgi
  have hnot : ¬ LogPairIsKlt c f (q * d) (q • D + (d * a) • G) := by
    intro h
    have hh := logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f _ _ h cT ⟨ξ i₀, hξ i₀⟩
    rw [hnewcrit] at hh
    exact lt_irrefl _ hh
  exact ⟨a, q, ha, hq, div_pos (by exact_mod_cast ha) (by exact_mod_cast hq),
    hLc, hnot, htestLC, W, hW, hWG, fun hOld => havoid W hOld hWG⟩

end MixedFujita
