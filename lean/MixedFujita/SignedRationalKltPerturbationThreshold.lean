/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCRationalKltThreshold
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.RationalThresholdLogCanonical

/-!
From a signed sub-klt pair and a nonzero effective Cartier divisor, construct the
exact positive rational endpoint of all-model klt perturbations and an actual
prime computing it. The joint SNC model and positive coefficient are internal.
No effectivity of the original boundary is required. The endpoint is log canonical
and excluded from klt. Restriction over a generic
base prime and a global discriminant divisor remain separate tasks.
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



variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A signed original klt pair has an exact finite rational fixed-divisor
threshold with an lc endpoint, without an effective-original-boundary input. -/
theorem exists_exact_rational_signed_klt_perturbation_threshold
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (G : CartierDivisor X) (hG : G.IsEffective) (hne : G ≠ 0) :
    ∃ (a q₀ : ℕ), 1 ≤ a ∧ 1 ≤ q₀ ∧ 0 < (a : ℚ) / q₀ ∧
      LogPairIsLogCanonical c f (q₀ * d) (q₀ • D + (d * a) • G) ∧
      (¬ LogPairIsKlt c f (q₀ * d) (q₀ • D + (d * a) • G)) ∧
      ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKlt c f (q * d) (q • D + (d * p) • G) ↔
          (p : ℚ) / q < (a : ℚ) / q₀) ∧
        (LogPairIsLogCanonical c f (q * d) (q • D + (d * p) • G) ↔
          (p : ℚ) / q ≤ (a : ℚ) / q₀) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hGsupp⟩ :=
    exists_proper_snc_model_with c f d D (fun _ : PUnit.{1} => G)
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨t, ht⟩ := proper_birational_effective_pullback_exists_positive_prime
    hnorm hnormT ρ hρ G hG hne
  have htin : (t : T) ∈ Set.range ξ := by
    by_contra hnot
    have hzero := hGsupp PUnit.unit t hnot
    rw [hzero] at ht
    exact lt_irrefl 0 ht
  obtain ⟨i, hi⟩ := htin
  have hpos : ∃ i, 0 < cartierCoefficient (cartierPullback ρ G) (ξ i) :=
    ⟨i, by simpa only [hi] using ht⟩
  obtain ⟨a, q₀, i₀, ha, hq₀, hgi, hratio, hendpoint, htest⟩ :=
    exists_snc_rational_klt_perturbation_threshold ρ hρ c f d hd D G hklt hG cT
      ξ hinj hcoh hsnc hsupp (hGsupp PUnit.unit) hpos
  have hnot : ¬ LogPairIsKlt c f (q₀ * d) (q₀ • D + (d * a) • G) := by
    intro h
    have hbound := h T ρ hρ cT (ξ i₀) (hcoh i₀)
    rw [hendpoint] at hbound
    exact lt_irrefl _ hbound
  have hlc := logPairIsLogCanonical_at_rational_klt_endpoint c f d D G a q₀ ha hq₀
    (fun p q hq hp => (htest p q hq).mpr hp)
  have hthresholdpos : (0 : ℚ) < (a : ℚ) / q₀ :=
    div_pos (by exact_mod_cast ha) (by exact_mod_cast hq₀)
  refine ⟨a, q₀, ha, hq₀, hthresholdpos, hlc, hnot, ?_⟩
  intro p q hq
  refine ⟨htest p q hq, ?_⟩
  constructor
  · intro h
    have hbound := h T ρ hρ cT (ξ i₀) (hcoh i₀)
    have hB : cartierCoefficient (crepantBoundaryCartier ρ hρ c f (q * d)
        (q • D + (d * p) • G) cT etaleCharts_cover) (ξ i₀) ≤ ((q * d : ℕ) : ℤ) := by
      rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
      omega
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
      cartierCoefficient_nsmul] at hB
    rw [hratio]
    exact (integer_perturbation_coefficient_le_iff _ _ d p q hd hq hgi).mp hB
  · intro hpq
    by_cases hp : 1 ≤ p
    · apply logPairIsLogCanonical_at_rational_klt_endpoint c f d D G p q hp hq
      intro x y hy hxy
      exact (htest x y hy).mpr (hxy.trans_le hpq)
    · have hpzero : p = 0 := by omega
      apply logPairIsKlt_logCanonical c f (q * d) (q • D + (d * p) • G)
      apply (htest p q hq).mpr
      simpa only [hpzero, Nat.cast_zero, zero_div] using hthresholdpos

end MixedFujita
