/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EtaleCartierHighOrderSections
public import MixedFujita.AmpleCartierEulerLimit
public import MixedFujita.CartierVanishingOrder

/-! 特異源ampleの全大倍数・全smooth閉点の実集中因子。 See reports/check-253-singular-concentration-nonLC-point.json for the verified scope. Actual etale chart completions evaluate original global Cartier sections on a possibly singular integral source, without global smoothness. Original normal klt BPF data with positive numerical dimension construct all-high-power concentrated effective divisors at smooth closed points, without an initial L section or KV. Actual high regular-equation order obstructs the original all-model pointwise log-canonical and klt predicates. A boundary-free closed point in any nonempty open and effective non-lc perturbations are constructed internally. Initial and restricted nonvanishing, lc-threshold ample preservation, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower


/-- An ample self-intersection above a coarse explicit threshold supplies high
intrinsic order at EVERY smooth closed point, uniformly for all sufficiently large powers.
The whole source may be singular. No high-order section, cohomology vanishing or section growth is supplied. -/
theorem proper_ample_large_diagonal_exists_smoothLocus_high_order_sections
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (A : CartierDivisor X)
    (hA : CartierIsAmpleProj K A) (r : ℕ)
    (hvolume : ((r + 1 : ℕ) : ℝ) ^ n <
      (cartierMixedEulerDifference K (List.replicate n A) 0 : ℝ) / n.factorial) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∀ x : X, IsClosed {x} → x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus →
      ∃ s : Γ((j • A).sheaf, ⊤), s ≠ 0 ∧
        ((r * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder (j • A) x s := by
  have hlim := proper_ample_cartier_sections_scaled_limit K n hdim.le A 0 hA
  have hzero (j : ℕ) : Module.finrank K Γ((0 + j • A).sheaf, ⊤) =
      Module.finrank K Γ((j • A).sheaf, ⊤) :=
    moduleSections_finrank_congr K (eqToIso (congrArg CartierDivisor.sheaf (zero_add (j • A))))
  have hevent : ∀ᶠ j : ℕ in atTop,
      ((r + 1 : ℕ) : ℝ) ^ n < (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) / (j : ℝ) ^ n := by
    filter_upwards [hlim.eventually (lt_mem_nhds hvolume)] with j hj
    rwa [hzero j] at hj
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hevent
  refine ⟨max j₀ 1, le_max_right _ _, ?_⟩
  intro j hj x hx hxsm
  have hjpos : 1 ≤ j := (le_max_right _ _).trans hj
  have hjR : (0 : ℝ) < j := by exact_mod_cast hjpos
  have hgrowth := (lt_div_iff₀ (pow_pos hjR n)).mp (hj₀ j ((le_max_left _ _).trans hj))
  have hbox : (r * j + 1) ^ n ≤ ((r + 1) * j) ^ n := by
    apply Nat.pow_le_pow_left
    nlinarith
  have hlarge : (r * j + 1) ^ n < Module.finrank K Γ((j • A).sheaf, ⊤) := by
    have hboxR : ((r * j + 1 : ℕ) : ℝ) ^ n ≤ ((r + 1 : ℕ) : ℝ) ^ n * (j : ℝ) ^ n := by
      exact_mod_cast (show (r * j + 1) ^ n ≤ (r + 1) ^ n * j ^ n by simpa only [mul_pow] using hbox)
    exact_mod_cast hboxR.trans_lt hgrowth
  exact smoothLocus_closedPoint_exists_high_order_section_of_finrank_gt_box n hdim (j • A) x hxsm hx
    (r * j) hlarge


/-- The coarse ample-volume criterion constructs ACTUAL effective Cartier
divisors linearly equivalent to every high power, with actual nonzero regular
local equations of high maximal-ideal order at every smooth closed point of the possibly singular source. -/
theorem proper_ample_large_diagonal_exists_smoothLocus_effective_concentration_divisors
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (A : CartierDivisor X)
    (hA : CartierIsAmpleProj K A) (r : ℕ)
    (hvolume : ((r + 1 : ℕ) : ℝ) ^ n <
      (cartierMixedEulerDifference K (List.replicate n A) 0 : ℝ) / n.factorial) :
    ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∀ x : X, IsClosed {x} → x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus →
      ∃ M : CartierDivisor X, M.IsEffective ∧
        (∃ u : X.functionFieldˣ, M = j • A + principalCartierDivisor X u) ∧
        ∃ (g : X.functionFieldˣ) (z : X.presheaf.stalk x), z ≠ 0 ∧
          algebraMap (X.presheaf.stalk x) X.functionField z = (g : X.functionField) ∧
          M.IsLocalEquationAt x g ∧ ((r * j : ℕ) : ℕ∞) < localAdicOrder (X.presheaf.stalk x) z := by
  obtain ⟨j₀, hj₀, hsec⟩ := proper_ample_large_diagonal_exists_smoothLocus_high_order_sections
    K n hdim A hA r hvolume
  refine ⟨j₀, hj₀, ?_⟩
  intro j hj x hx hxsm
  obtain ⟨s, hs, horder⟩ := hsec j hj x hx hxsm
  obtain ⟨f, hf⟩ := (j • A).exists_isLocalEquationAt x
  obtain ⟨z, hz, himage, heq, hord⟩ := cartierSectionZeroDivisor_regular_localEquation
    (j • A) x f hf s hs
  exact ⟨cartierSectionZeroDivisor (j • A) s hs, cartierSectionZeroDivisor_isEffective _ _ _,
    ⟨cartierSectionUnit (j • A) s hs, rfl⟩, f * cartierSectionUnit (j • A) s hs,
    z, hz, himage, heq, by rwa [hord]⟩

end MixedFujita
