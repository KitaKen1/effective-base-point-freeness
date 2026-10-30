/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IntegerLinearNonnegativeSlope
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.MixedAmpleCartierIntersection
public import MixedFujita.TopMixedEulerHomogeneity

/-! 任意本数の元nef因子の実最高次混合非負性。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- ANY number of original curve-test nef factors, together with any ample
tail, has nonnegative top mixed coefficient. No nef factor is assumed semiample. -/
theorem proper_nef_ample_cartierMixedEuler_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    (N H : List (CartierDivisor X)) (hlen : N.length + H.length = n)
    (hN : ∀ D ∈ N, CartierIsNef K D) (hH : ∀ D ∈ H, CartierIsAmpleProj K D)
    (E : CartierDivisor X) : 0 ≤ cartierMixedEulerDifference K (N ++ H) E := by
  induction N generalizing H with
  | nil =>
    simp only [List.nil_append]
    exact (proper_ample_cartierMixedEuler_positive K n hdim hn H (by simpa using hlen) hH E).le
  | cons D N ih =>
    have hD : CartierIsNef K D := hN D (List.mem_cons_self ..)
    have hN' : ∀ F ∈ N, CartierIsNef K F := fun F hF => hN F (List.mem_cons_of_mem _ hF)
    apply int_nonneg_of_all_nat_mul_add_nonneg
      (cartierMixedEulerDifference K (D :: (N ++ H)) E)
      (cartierMixedEulerDifference K (A :: (N ++ H)) E)
    intro m
    have hma : CartierIsAmpleProj K (m • D + A) :=
      proper_nef_add_ample_isAmpleProj K _ _ (cartierIsNef_nsmul hD m) hA
    have h := ih ((m • D + A) :: H)
      (by simp only [List.length_cons] at *; omega) hN' (by
        intro F hF
        rcases List.mem_cons.mp hF with rfl | hF
        · exact hma
        · exact hH F hF)
    have perm : (N ++ (m • D + A) :: H).Perm ((m • D + A) :: (N ++ H)) :=
      List.perm_append_comm.trans (List.perm_append_comm.cons _)
    rw [cartierMixedEulerDifference_perm K perm E] at h
    have hlen' : (N ++ H).length + 1 = n := by
      simp only [List.length_append, List.length_cons] at *
      omega
    rw [proper_cartierMixedEulerDifference_top_add_first K n hdim.le (N ++ H) hlen' (m • D) A E] at h
    have hs := proper_cartierMixedEulerDifference_top_nsmul_factor K n hdim.le [] (N ++ H)
      (by simpa only [List.length_nil, zero_add] using hlen') D E m
    simp only [List.nil_append] at hs
    rw [hs] at h
    exact h


/-- Every top-dimensional family of original curve-test nef divisors has
nonnegative original mixed coefficient, without global generation assumptions. -/
theorem proper_nef_cartierMixedEuler_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hProj : ∃ A : CartierDivisor X, CartierIsAmpleProj K A)
    (D : List (CartierDivisor X)) (hlen : D.length = n)
    (hD : ∀ F ∈ D, CartierIsNef K F) (E : CartierDivisor X) :
    0 ≤ cartierMixedEulerDifference K D E := by
  obtain ⟨A, hA⟩ := hProj
  simpa only [List.append_nil] using proper_nef_ample_cartierMixedEuler_nonneg
    K n hdim hn A hA D [] (by simpa using hlen) hD (by simp) E


/-- Ordinary original mixed intersections of arbitrary nef families are
nonnegative, with no semiample condition on any factor. -/
theorem proper_nef_cartierMixedIntersection_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hProj : ∃ A : CartierDivisor X, CartierIsAmpleProj K A)
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length)
    (hne : D ≠ []) (hD : ∀ F ∈ D, CartierIsNef K F) :
    0 ≤ cartierMixedIntersection K D hdim := by
  exact proper_nef_cartierMixedEuler_nonneg K D.length hdim
    (by have := List.length_pos_iff.mpr hne; omega) hProj D rfl hD 0


/-- General nef mixed nonnegativity includes all lower-dimensional proper
integral sources, where geometric nilpotence supplies zero automatically. -/
theorem proper_nef_cartierMixedEuler_nonneg_of_dim_le
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ))
    (hProj : ∃ A : CartierDivisor X, CartierIsAmpleProj K A)
    (D : List (CartierDivisor X)) (hlen : D.length = n + 1)
    (hD : ∀ F ∈ D, CartierIsNef K F) (E : CartierDivisor X) :
    0 ≤ cartierMixedEulerDifference K D E := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, topologicalKrullDim X = k :=
    ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
  have hkn : k ≤ n + 1 := by rw [hk] at hdim; exact_mod_cast hdim
  by_cases heq : k = n + 1
  · exact proper_nef_cartierMixedEuler_nonneg K k hk (by omega) hProj D (by omega) hD E
  · rw [proper_cartierMixedEulerDifference_vanish_of_length K k hk.le D (by omega) E]

end MixedFujita
