/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MinimalLCCriticalCoefficients
public import MixedFujita.LCThresholdPrimePlacement
public import MixedFujita.PositiveRationalLCThreshold
public import MixedFujita.MinimalLogCanonicalCenters
public import MixedFujita.StrictLCClosedCenterDimension
public import MixedFujita.IsolationRationalData

/-! 全旧中心回避なしの実有理閾値と低次元新極小整lc中心。 See reports/check-258-minimal-lc-section-adjoint-descent.json for the verified scope. Inclusion-minimality and exterior LC force zero perturbation at every old critical prime, removing the all-old-center avoidance premise. Nonzero NATURAL restriction is equivalent to noncontainment in the actual zero-divisor support. The same threshold-prime strict old discrepancy places its center inside the original minimal center. An exact positive rational threshold and a lower-dimensional inclusion-minimal integral new-pair lc center are constructed internally. Actual original ample-adjoint sections preserve all-large ORIGINAL L ample adjoints. Exterior LC and an actual ambient non-LC point remain explicit hypotheses. Their construction from restricted concentration, appropriate center vanishing, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Starting at an inclusion-minimal actual lc center, exterior lc, noncontainment
in the effective perturbation and an actual non-lc point internally construct
an exact positive rational threshold and an inclusion-minimal new lc center of
STRICTLY smaller ordinary geometric dimension. No all-old-center avoidance,
center normality, intersection theorem, original KLT or supplied threshold/model
is assumed. Exterior lc and the actual non-lc point remain explicit inputs. -/
theorem minimal_lc_center_concentration_exists_strict_lower_dimensional_center
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (M : CartierDivisor X) (hM : M.IsEffective)
    (hZnot : ¬ Z ≤ (effectiveCartierIdealSheaf M hM).support)
    (j : ℕ) (hj : 1 ≤ j) (x : X)
    (hnonLC : ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M))
    (houtside : ∀ y : X, y ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) y c f (j * d) (j • D + M))
    (k : ℕ) (hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (k + 1 : ℕ)) :
    ∃ a q : ℕ, 1 ≤ a ∧ 1 ≤ q ∧ d * a * j < q ∧
      LogPairBoundaryEffective c f (q * d) (q • D + (d * a) • M) ∧
      LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • M) ∧
      (¬ LogPairIsKlt c f (q * d) (q • D + (d * a) • M)) ∧
      (∀ p v : ℕ, 1 ≤ v →
        (LogPairIsLogCanonical c f (v * d) (v • D + (d * p) • M) ↔ (p : ℚ) / v ≤ (a : ℚ) / q)) ∧
      ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) W ∧
        (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) V → V ≤ W → V = W) ∧
        W < Z ∧ W ≤ (effectiveCartierIdealSheaf M hM).support ∧
        IsIntegral (Scheme.IdealSheafData.vanishingIdeal W).subscheme ∧
        topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal W).subscheme ≤ k := by
  classical
  have hlc := hZ.1
  have hjd : 1 ≤ j * d := Nat.mul_pos (by omega) (by omega)
  have hne : M ≠ 0 := by
    intro hzero
    have h := (logPairIsLogCanonical_scale_denominator_iff c f d j hj D).mpr hlc
    apply hnonLC
    rw [hzero, add_zero]
    exact logPairIsLogCanonical_overBasePoint (𝟙 X) x c f (j * d) (j • D) h
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, hMsupp⟩ :=
    exists_proper_snc_model_with c f d D (fun _ : PUnit.{1} => M)
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
    hnorm hnormT ρ hρ M hM hne
  have htin : (t : T) ∈ Set.range ξ := by
    by_contra h
    rw [hMsupp PUnit.unit t h] at ht
    exact lt_irrefl _ ht
  obtain ⟨i, hi⟩ := htin
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let b (i : Fin r) := cartierCoefficient B (ξ i)
  let g (i : Fin r) := cartierCoefficient (cartierPullback ρ M) (ξ i)
  have hb (i : Fin r) : b i ≤ (d : ℤ) :=
    logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hlc cT ⟨ξ i, hξ i⟩
  have hg (i : Fin r) : 0 ≤ g i :=
    cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ M hM) (ξ i)
  have hcritical (i : Fin r) (hi : b i = (d : ℤ)) : g i = 0 :=
    minimal_lc_center_exterior_lc_forces_critical_pullback_coefficient_zero ρ hρ c f d D hlc M hM
      j Z hmin hZnot houtside cT (ξ i) (hξ i) hi
  have hpos : ∃ i, 0 < g i := ⟨i, by simpa only [g, hi] using ht⟩
  obtain ⟨a, q, i₀, ha, hq, hgi, hbi, _, hendpoint, htest⟩ :=
    finite_integer_lc_coefficients_exact_threshold b g d hd hb hg hcritical hpos
  have htestLC (p v : ℕ) (hv : 1 ≤ v) :
      LogPairIsLogCanonical c f (v * d) (v • D + (d * p) • M) ↔ (p : ℚ) / v ≤ (a : ℚ) / q :=
    (logPairIsLogCanonical_rational_perturbation_iff_snc_coefficients ρ hρ c f d hd D M
      cT ξ hinj hξ hsnc hsupp (hMsupp PUnit.unit) p v hv).trans (htest p v hv)
  have hLc := (htestLC a q hq).mpr le_rfl
  have hbad : ¬ LogPairIsLogCanonical c f ((j * d) * d)
      ((j * d) • D + (d * 1) • M) := by
    intro h
    apply hnonLC
    apply logPairIsLogCanonical_overBasePoint (𝟙 X) x c f (j * d) (j • D + M)
    apply (logPairIsLogCanonical_scale_denominator_iff c f (j * d) d hd (j • D + M)).mp
    have hpres : d • (j • D + M) = (j * d) • D + (d * 1) • M := by
      simp only [smul_add, smul_smul, mul_one, Nat.mul_comm]
    rwa [Nat.mul_comm d (j * d), hpres]
  have hratio : (a : ℚ) / q < (1 : ℚ) / (j * d : ℕ) := by
    apply lt_of_not_ge
    exact fun h => hbad ((htestLC 1 (j * d) hjd).mpr h)
  have hcross := (div_lt_div_iff₀ (by exact_mod_cast hq : (0 : ℚ) < q)
    (by exact_mod_cast hjd : (0 : ℚ) < (j * d : ℕ))).mp hratio
  have hsmall : d * a * j < q := by
    have hcross' : (a : ℚ) * (j * d : ℕ) < q := by simpa only [one_mul] using hcross
    have hp : a * (j * d) < q := by exact_mod_cast hcross'
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hp
  have hnewcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q * d)
      (q • D + (d * a) • M) cT etaleCharts_cover) (ξ i₀) = ((q * d : ℕ) : ℤ) := by
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_nsmul]
    exact hendpoint
  have hnewdis : cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f (q * d)
      (q • D + (d * a) • M) cT etaleCharts_cover) (ξ i₀) = -((q * d : ℕ) : ℤ) := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg] at hnewcrit
    omega
  have holdstrict : -(d : ℤ) < cartierCoefficient
      (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) (ξ i₀) := by
    change cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i₀) < (d : ℤ) at hbi
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg] at hbi
    omega
  let C : Closeds X := ⟨closure ({ρ (ξ i₀)} : Set X), isClosed_closure⟩
  have hC : LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) C :=
    crepant_critical_prime_is_logCanonicalCenter ρ hρ c f (q * d) _ hLc cT (ξ i₀) (hξ i₀) hnewcrit
  have hCZ : C ≤ Z := strict_lc_perturbation_prime_center_le_closed_of_old_discrepancy_strict
    ρ hρ c f d a q j hsmall D M Z houtside cT (ξ i₀) (hξ i₀) holdstrict hnewdis
  have hCM : C ≤ (effectiveCartierIdealSheaf M hM).support :=
    positive_effective_pullback_prime_center_le_source_support ρ M hM (ξ i₀) hgi
  have hClt : C < Z := lt_of_le_of_ne hCZ (fun heq => hZnot (heq ▸ hCM))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  let : IsNoetherian X := {}
  obtain ⟨W, hWC, hW, hminW⟩ := logCanonicalCenter_contains_minimal_center c f (q * d) _ C hC
  have hWlt : W < Z := lt_of_le_of_lt hWC hClt
  have heffq := (logPairBoundaryEffective_scale_denominator_iff c f d q hq D).mpr heff
  exact ⟨a, q, ha, hq, hsmall,
    logPairBoundaryEffective_add_effective c f (q * d) _ _ heffq
      (cartier_nsmul_isEffective M hM (d * a)), hLc,
    fun hk => (lt_irrefl _) (hnewcrit ▸ logPairIsKlt_crepantBoundary_coefficient_lt
      ρ hρ c f _ _ hk cT ⟨ξ i₀, hξ i₀⟩), htestLC, W, hW, hminW, hWlt, hWC.trans hCM,
    logCanonicalCenter_reduced_subscheme_isIntegral c f (q * d) _ W hW,
    strict_subcenter_reduced_subscheme_dimension_drop c f d D Z hZ W hWlt k hdim⟩

end MixedFujita
