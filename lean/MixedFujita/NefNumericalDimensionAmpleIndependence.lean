/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefMixedEulerMonotonicity
public import MixedFujita.CartierNumericalDimension
public import MixedFujita.AmpleEffectiveComparison

/-! 任意nefの元混合冪正値性・数値次元の補助ample非依存。 See reports/check-252-positive-numerical-concentration-ample-independence.json for the verified scope. Finite Taylor boxes and actual ample Hilbert limits construct actual high-order effective concentration divisors at every closed point in all high powers. Positive original mixed-intersection numerical dimension gives the explicit ample pencil parameter. Original nef numerical dimension is ample-independent without semiampleness. Smooth original klt BPF data construct normalized high-order cuts without an initial L section or KV. Initial and restricted nonvanishing, singular-source local smooth-point extension, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- For any ORIGINAL nef divisor, positivity of each ordinary mixed power is
independent of the auxiliary ample divisor. No semiampleness is assumed. -/
theorem proper_nef_cartierMixedPower_positive_iff_ample_base
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J H : CartierDivisor X) (hD : CartierIsNef K D)
    (hJ : CartierIsAmpleProj K J) (hH : CartierIsAmpleProj K H) (k : Fin (n + 1)) :
    0 < cartierMixedPowerIntersection K n hdim D J k ↔
      0 < cartierMixedPowerIntersection K n hdim D H k := by
  have transfer : ∀ (J H : CartierDivisor X), CartierIsAmpleProj K J → CartierIsAmpleProj K H →
      0 < cartierMixedPowerIntersection K n hdim D J k →
        0 < cartierMixedPowerIntersection K n hdim D H k := by
    intro J H hJ hH hpos
    obtain ⟨q₀, hq₀⟩ := cartierIsAmpleProj_eventually_twist_veryAmple hH (-J)
    let q := max q₀ 1
    have hq : 1 ≤ q := le_max_right _ _
    have hdiff : CartierIsNef K (q • H - J) := by
      apply cartierIsAmpleProj_isNef
      apply cartierIsAmpleProj_of_veryAmple
      simpa only [sub_eq_add_neg, add_comm] using hq₀ q (le_max_left _ _)
    let P := List.replicate k.val D
    let T := List.replicate (n - k.val) J
    have hlen : P.length + T.length = n := by
      simp only [P, T, List.length_replicate]
      omega
    have hT : ∀ F ∈ T, CartierIsNef K F := by
      intro F hF
      rw [List.eq_of_mem_replicate hF]
      exact cartierIsAmpleProj_isNef hJ
    have hdiffT : ∀ F ∈ T, CartierIsNef K (q • H - F) := by
      intro F hF
      rwa [List.eq_of_mem_replicate hF]
    have hmono := proper_nef_cartierMixedEuler_le_repeated_factor K n hdim hn ⟨H, hH⟩
      (q • H) (cartierIsNef_nsmul (cartierIsAmpleProj_isNef hH) q) P T hlen
      (fun F hF => (List.eq_of_mem_replicate hF) ▸ hD) hT hdiffT 0
    change 0 < cartierMixedEulerDifference K
      (List.replicate k.val D ++ List.replicate (n - k.val) J) 0 at hpos
    have hpos' : 0 < cartierMixedEulerDifference K
        (List.replicate k.val D ++ List.replicate (n - k.val) (q • H)) 0 := by
      exact lt_of_lt_of_le hpos (by simpa only [P, T, List.length_replicate] using hmono)
    have hscale := proper_cartierMixedEulerDifference_top_nsmul_prefix K n hdim.le
      (List.replicate (n - k.val) H) (List.replicate k.val D)
      (by simp only [List.length_replicate]; omega) 0 q
    simp only [List.map_replicate, List.length_replicate] at hscale
    rw [cartierMixedEulerDifference_perm K List.perm_append_comm 0, hscale,
      cartierMixedEulerDifference_perm K List.perm_append_comm 0] at hpos'
    exact (mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hq : (0 : ℤ) < q) _)).mp hpos'
  exact ⟨transfer J H hJ hH, transfer H J hH hJ⟩


/-- The ORIGINAL maximum of positive mixed powers of an arbitrary nef divisor
is independent of the auxiliary ample divisor, without Iitaka or semiampleness. -/
theorem proper_nef_cartierNumericalDimension_ample_independent
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J H : CartierDivisor X) (hD : CartierIsNef K D)
    (hJ : CartierIsAmpleProj K J) (hH : CartierIsAmpleProj K H) :
    cartierNumericalDimension K n hdim D J = cartierNumericalDimension K n hdim D H := by
  unfold cartierNumericalDimension
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact proper_nef_cartierMixedPower_positive_iff_ample_base K n hdim hn D J H hD hJ hH k

end MixedFujita
