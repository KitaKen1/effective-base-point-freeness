/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalPrimeCentres
public import MixedFujita.FixedPrimeCoefficientLocus
public import MixedFujita.ThresholdModelLifting

/-!
At a codimension-one point of a smooth integral base, every divisorial test whose centre
contains the point has exactly that centre and the same DVR valuation and discrepancy. Thus
the full existential realization relation equals the identity-model prime test. This is a
proved exhaustive reduction, not a chosen finite-test hypothesis. Consequently the full tuple
coefficient closedness statement holds at every such point, with no section-rank restriction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
open scoped BigOperators

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian Y]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- At a smooth base prime all tests in the original realization definition reduce to the
identity prime. Values and discrepancies agree, including at threshold equality. -/
theorem isRealizedProfile_iff_identityPrime_at_codimOne (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (x : Y)
    (hx : Order.coheight x = 1) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (α : Fin N → ℝ) :
    IsRealizedProfile cY fY d D₀ D x s α ↔
      PrimeTestRealizesProfile (𝟙 Y) (dominantFunctionFieldMap_id_bijective (X := Y))
        cY fY d D₀ D cY ⟨x, hx⟩ x s α := by
  constructor
  · rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcentre, hpos, hval⟩
    have he : σ (e : U) = x := birational_prime_image_eq_of_mem_closure σ hσ hx e hcentre
    have hξ : Order.coheight (σ (e : U)) = 1 := by rw [he]; exact hx
    have hb := stalkMap_bijective_of_birational_over_smooth_prime (n := n) σ hσ (e : U) hξ
    have hsmY : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    have hsmU : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    have hdvrY := smoothOverField_codimensionOne_stalk_DVR (K := K) ⟨σ (e : U), hξ⟩
    have hdvrU := smoothOverField_codimensionOne_stalk_DVR (K := K) e
    have hdisc : cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU
        etaleCharts_cover) (e : U) = cartierCoefficient (logDiscrepancyDivisor n (𝟙 Y)
          (dominantFunctionFieldMap_id_bijective (X := Y)) cY fY d D₀ cY etaleCharts_cover) x := by
      have h := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective (𝟙 Y) σ
        (dominantFunctionFieldMap_id_bijective (X := Y)) hσ cY fY d D₀ cY cU e hξ hb
      simpa only [Category.comp_id, he] using h
    refine ⟨subset_closure rfl, ?_, fun i hsi => ?_⟩
    · simpa only [hdisc] using hpos
    · have hvi := cartierCoefficient_pullback_of_stalkMap_bijective σ e hξ hb
        (cartierSectionZeroDivisor D (s i) hsi)
      rw [he] at hvi
      have h := hval i hsi
      rw [hdisc, hvi] at h
      simpa only [cartierPullback_id] using h
  · exact isRealizedProfile_of_primeTest (𝟙 Y) (dominantFunctionFieldMap_id_bijective (X := Y))
      cY fY d D₀ D cY ⟨x, hx⟩ x s α

/-- The unrestricted realization locus of polynomial section combinations is actually closed
in coefficients at a smooth codimension-one base point. Every test model has been accounted for. -/
theorem exists_polynomialIdeal_realization_at_codimOne {τ : Type*} [Finite τ]
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y)
    (x : Y) (hx : Order.coheight x = 1) {N m : ℕ} (b : Fin m → Γ(D.sheaf, ⊤))
    (L : Fin N → Fin m → MvPolynomial τ K) (α : Fin N → ℝ) :
    ∃ I : Ideal (MvPolynomial τ K),
      {c : τ → K | IsRealizedProfile cY fY d D₀ D x
        (fun i => ∑ k, MvPolynomial.eval c (L i k) • b k) α} = polynomialZeroSet I := by
  obtain ⟨I, hI⟩ := exists_polynomialIdeal_primeTest (𝟙 Y)
    (dominantFunctionFieldMap_id_bijective (X := Y)) cY fY d D₀ D cY ⟨x, hx⟩ x b L α
  refine ⟨I, ?_⟩
  rw [← hI]
  ext c
  exact isRealizedProfile_iff_identityPrime_at_codimOne cY fY d D₀ D x hx _ α

/-- The full Lemma-3 tuple interface at a smooth codimension-one point; arbitrary finite
families and all their coefficient matrices are included. -/
theorem realizationSetsZariskiClosed_at_smoothPrime (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (x : Y)
    (hx : Order.coheight x = 1) : RealizationSetsZariskiClosed cY fY d D₀ D x := by
  intro N m b α _
  obtain ⟨I, hI⟩ := exists_polynomialIdeal_realization_at_codimOne cY fY d D₀ D x hx b
    (fun i k => MvPolynomial.X (i, k)) (fun i => (α i : ℝ))
  exact ⟨I, by simpa only [MvPolynomial.eval_X] using hI⟩

end MixedFujita
