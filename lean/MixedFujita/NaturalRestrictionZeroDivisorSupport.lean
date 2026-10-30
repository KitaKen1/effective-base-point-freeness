/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualCartierPullbackNonvanishing
public import MixedFujita.CartierSectionZeroIdeal

/-! 自然制限非零と実零因子の台への非包含の同値。 See reports/check-258-minimal-lc-section-adjoint-descent.json for the verified scope. Inclusion-minimality and exterior LC force zero perturbation at every old critical prime, removing the all-old-center avoidance premise. Nonzero NATURAL restriction is equivalent to noncontainment in the actual zero-divisor support. The same threshold-prime strict old discrepancy places its center inside the original minimal center. An exact positive rational threshold and a lower-dimensional inclusion-minimal integral new-pair lc center are constructed internally. Actual original ample-adjoint sections preserve all-large ORIGINAL L ample adjoints. Exterior LC and an actual ambient non-LC point remain explicit hypotheses. Their construction from restricted concentration, appropriate center vanishing, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- For any actual integral closed subscheme, NONZERO NATURAL restriction of a
section is equivalent to its support not being contained in the support of the
actual effective zero divisor. No center normality, dominance or KV is needed. -/
theorem natural_restriction_ne_zero_iff_not_le_zero_divisor_support
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (P : CartierDivisor X) (s : Γ(P.sheaf, ⊤)) (hs : s ≠ 0) :
    modulePullbackGlobalSections I.subschemeι P.sheaf s ≠ 0 ↔
      ¬ I.support ≤ (effectiveCartierIdealSheaf (cartierSectionZeroDivisor P s hs)
        (cartierSectionZeroDivisor_isEffective P s hs)).support := by
  rw [cartierActualGlobalPullback_ne_zero_iff_image_meets_nonvanishingOpen]
  have hsupp : ((effectiveCartierIdealSheaf (cartierSectionZeroDivisor P s hs)
      (cartierSectionZeroDivisor_isEffective P s hs)).support : Set X) = cartierSectionZeroLocus P s :=
    cartierSectionZeroIdeal_support (K := K) P s hs
  constructor
  · rintro ⟨y, hy⟩ hle
    have hyI : I.subschemeι y ∈ I.support := by
      change I.subschemeι y ∈ (I.support : Set X)
      rw [← I.range_subschemeι]
      exact Set.mem_range_self y
    have hz := hle hyI
    rw [show I.subschemeι y ∈ (effectiveCartierIdealSheaf (cartierSectionZeroDivisor P s hs)
      (cartierSectionZeroDivisor_isEffective P s hs)).support ↔ I.subschemeι y ∈ cartierSectionZeroLocus P s from
      Set.ext_iff.mp hsupp _] at hz
    exact hz hy
  · intro hnot
    by_contra h
    apply hnot
    intro x hx
    change x ∈ (I.support : Set X) at hx
    rw [← I.range_subschemeι] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [show I.subschemeι y ∈ (effectiveCartierIdealSheaf (cartierSectionZeroDivisor P s hs)
      (cartierSectionZeroDivisor_isEffective P s hs)).support ↔ I.subschemeι y ∈ cartierSectionZeroLocus P s from
      Set.ext_iff.mp hsupp _]
    exact fun hy => h ⟨y, hy⟩

end MixedFujita
