/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCRoundupSplitArithmetic

/-! lc roundup負係数と係数一臨界成分の一致。 See reports/check-247-lc-non-klt-support-canonical-subscheme.json for the verified scope. The actual lc kernel image support equals the original all-model non-klt locus. Its radical coherent ideal and nonempty reduced lower-dimensional W are unique, independent of the SNC model and adjoint P, and constructed without KV. Containment in any closed Z is equivalent to klt outside Z. Usual KV is a condition only for simultaneous restriction lifting. Stable-base-locus perturbation, restricted-section nonvanishing, usual KV, normal minimal-lc-center adjunction, klt BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

/-- An lc roundup has a negative coefficient exactly at a coefficient-one component. -/
theorem lc_negative_boundary_roundup_negative_iff_critical
    (b : ℤ) (d : ℕ) (hd : 1 ≤ d) (hb : b ≤ (d : ℤ)) :
    ⌈-((b : ℝ) / (d : ℝ))⌉ < 0 ↔ b = (d : ℤ) := by
  by_cases he : b = (d : ℤ)
  · have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    norm_num [he, hd0]
  · have hn := lc_roundup_positive_part_nonneg b d hd hb
    rw [ite_eq_right he, add_zero] at hn
    omega

end MixedFujita
