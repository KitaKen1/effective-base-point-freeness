/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothPrimeRealization
public import MixedFujita.RealizationThresholdReduction

/-!
Actual local-ideal threshold realization, with all smooth birational models and prime divisors
quantified as in IdealThresholdZariskiClosed. At a smooth codimension-one base point all tests
reduce to the identity prime. Weak real order thresholds, including zero local functions, are
exactly membership in a natural power of the base maximal ideal.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The original existential test condition for local ideal generators, at a real multiple of
the discrepancy. Zero generators impose no inequality, as in the threshold interface. -/
def IsRealizedLocalIdealThreshold (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ : CartierDivisor Y) (x : Y) {J : Type*} (g : J → Y.presheaf.stalk x) (t : ℝ) : Prop :=
  ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
    (_ : U.Over (Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
    (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U),
    x ∈ closure ({σ (e : U)} : Set Y) ∧
    0 < ((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d ∧
    ∀ j, g j ≠ 0 → t * (((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) ≤
      (U.ord ((dominantFunctionFieldMap σ).hom
        (algebraMap (Y.presheaf.stalk x) Y.functionField (g j))) (e : U) : ℝ)

variable [IsLocallyNoetherian Y]

/-- A real prime-order threshold on a local function is exactly a maximal-ideal power
condition, with zero included and the weak threshold equality preserved. -/
theorem mem_maximalIdeal_pow_ceil_iff_primeOrder (x : CodimensionOnePoint Y)
    [IsDiscreteValuationRing (Y.presheaf.stalk (x : Y))]
    (a : Y.presheaf.stalk (x : Y)) (t : ℝ) :
    a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (x : Y)) ^ ⌈t⌉₊ ↔
      ∀ _ha : a ≠ 0, t ≤
        (Y.ord (algebraMap (Y.presheaf.stalk (x : Y)) Y.functionField a) (x : Y) : ℝ) := by
  by_cases ha : a = 0
  · subst a
    simp
  · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp
      (fun h => ha ((localAdicOrder_eq_top_iff a).mp h))
    have hord := scheme_ord_regular_eq_localAdicOrder_nat x a ha k hk.symm
    rw [← localAdicOrder_nat_le_iff, hk.symm]
    constructor
    · intro h _
      rw [hord]
      exact_mod_cast Nat.ceil_le.mp (show ⌈t⌉₊ ≤ k by exact_mod_cast h)
    · intro h
      have ht := h ha
      rw [hord] at ht
      exact_mod_cast (Nat.ceil_le.mpr (show t ≤ (k : ℝ) by exact_mod_cast ht))

variable [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- Every test of the actual local-ideal threshold condition at a smooth base prime has the
same value and discrepancy as the identity prime; all test models are accounted for. -/
theorem isRealizedLocalIdealThreshold_iff_identity_at_codimOne (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y) (x : Y)
    (hx : Order.coheight x = 1) {J : Type*} (g : J → Y.presheaf.stalk x) (t : ℝ) :
    IsRealizedLocalIdealThreshold cY fY d D₀ x g t ↔
      0 < ((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n (𝟙 Y)
        (dominantFunctionFieldMap_id_bijective (X := Y)) cY fY d D₀ cY etaleCharts_cover) x) / d ∧
      ∀ j, g j ≠ 0 → t * (((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n (𝟙 Y)
        (dominantFunctionFieldMap_id_bijective (X := Y)) cY fY d D₀ cY etaleCharts_cover) x) / d) ≤
        (Y.ord (algebraMap (Y.presheaf.stalk x) Y.functionField (g j)) x : ℝ) := by
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
    refine ⟨by simpa only [hdisc] using hpos, fun j hj => ?_⟩
    have hv := hval j hj
    have ho := scheme_ord_pullback_of_stalkMap_bijective σ e hξ hb
      (algebraMap (Y.presheaf.stalk x) Y.functionField (g j))
    rw [he] at ho
    simpa only [hdisc, ho] using hv
  · rintro ⟨hpos, hval⟩
    refine ⟨Y, inferInstance, inferInstance, inferInstance, inferInstance, 𝟙 Y,
      inferInstance, inferInstance, dominantFunctionFieldMap_id_bijective (X := Y), cY,
      ⟨x, hx⟩, subset_closure rfl, hpos, fun j hj => ?_⟩
    simpa only [dominantFunctionFieldMap_id, CommRingCat.hom_id, RingHom.id_apply] using hval j hj

end MixedFujita
