/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GeneralNefMixedEuler
public import MixedFujita.TopMixedEulerHomogeneity

/-! 任意nef最高次混合単調性と選択混合冪下界。 See reports/check-252-positive-numerical-concentration-ample-independence.json for the verified scope. Finite Taylor boxes and actual ample Hilbert limits construct actual high-order effective concentration divisors at every closed point in all high powers. Positive original mixed-intersection numerical dimension gives the explicit ample pencil parameter. Original nef numerical dimension is ample-independent without semiampleness. Smooth original klt BPF data construct normalized high-order cuts without an initial L section or KV. Initial and restricted nonvanishing, singular-source local smooth-point extension, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Replacing any actual nef factor by a nef sum can only increase its top
mixed Euler coefficient. This comparison keeps an arbitrary actual nef prefix. -/
theorem proper_nef_cartierMixedEuler_le_repeated_factor
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (A : CartierDivisor X) (hA : CartierIsNef K A)
    (P D : List (CartierDivisor X)) (hlen : P.length + D.length = n)
    (hP : ∀ F ∈ P, CartierIsNef K F) (hD : ∀ F ∈ D, CartierIsNef K F)
    (hdiff : ∀ F ∈ D, CartierIsNef K (A - F)) (E : CartierDivisor X) :
    cartierMixedEulerDifference K (P ++ D) E ≤
      cartierMixedEulerDifference K (P ++ List.replicate D.length A) E := by
  induction D generalizing P with
  | nil => simp
  | cons F D ih =>
    have hD' : ∀ G ∈ D, CartierIsNef K G := fun G hG => hD G (List.mem_cons_of_mem F hG)
    have hdiff' : ∀ G ∈ D, CartierIsNef K (A - G) :=
      fun G hG => hdiff G (List.mem_cons_of_mem F hG)
    have hnonneg := proper_nef_cartierMixedEuler_nonneg K n hdim hn hProj
      (P ++ (A - F) :: D) (by simp only [List.length_append, List.length_cons] at *; omega)
      (by
        intro G hG
        rcases List.mem_append.mp hG with hG | hG
        · exact hP G hG
        · rcases List.mem_cons.mp hG with rfl | hG
          · exact hdiff F (List.mem_cons_self ..)
          · exact hD' G hG) E
    have hadd := proper_cartierMixedEulerDifference_top_add_factor K n hdim.le P D
      (by simp only [List.length_cons] at hlen; omega) F (A - F) E
    rw [show F + (A - F) = A by abel] at hadd
    have hhead : cartierMixedEulerDifference K (P ++ F :: D) E ≤
        cartierMixedEulerDifference K (P ++ A :: D) E := by omega
    have htail := ih (P ++ [A])
      (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
      (by
        intro G hG
        rcases List.mem_append.mp hG with hG | hG
        · exact hP G hG
        · simpa only [List.mem_singleton.mp hG] using hA) hD' hdiff'
    simp only [List.append_assoc, List.singleton_append] at htail
    simpa only [List.length_cons, List.replicate_succ] using hhead.trans htail


/-- One selected positive original mixed power already grows without bound
inside the ample diagonal of lL+H. Binomial expansion is unnecessary. -/
theorem proper_nef_diagonal_ge_scaled_selected_mixed_power
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (k : ℕ) (hk : k ≤ n) (l : ℕ) (E : CartierDivisor X) :
    (l : ℤ) ^ k * cartierMixedEulerDifference K
        (List.replicate k L ++ List.replicate (n - k) H) E ≤
      cartierMixedEulerDifference K (List.replicate n (l • L + H)) E := by
  have hHnef := cartierIsAmpleProj_isNef hH
  have hlL := cartierIsNef_nsmul hL l
  let D := List.replicate k (l • L) ++ List.replicate (n - k) H
  have hlen : D.length = n := by simp only [D, List.length_append, List.length_replicate]; omega
  have hD : ∀ F ∈ D, CartierIsNef K F := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · exact (List.eq_of_mem_replicate hF) ▸ hlL
    · exact (List.eq_of_mem_replicate hF) ▸ hHnef
  have hdiff : ∀ F ∈ D, CartierIsNef K (l • L + H - F) := by
    intro F hF
    rcases List.mem_append.mp hF with hF | hF
    · rw [List.eq_of_mem_replicate hF, add_sub_cancel_left]
      exact hHnef
    · rw [List.eq_of_mem_replicate hF, add_sub_cancel_right]
      exact hlL
  have hmono := proper_nef_cartierMixedEuler_le_repeated_factor K n hdim hn ⟨H, hH⟩
    (l • L + H) (cartierIsNef_add hlL hHnef) [] D (by simpa using hlen) (by simp) hD hdiff E
  have hscale := proper_cartierMixedEulerDifference_top_nsmul_prefix K n hdim.le
    (List.replicate k L) (List.replicate (n - k) H)
    (by simp only [List.length_replicate]; omega) E l
  simp only [List.map_replicate, List.length_replicate] at hscale
  simpa only [List.nil_append, hlen, D, hscale] using hmono

end MixedFujita
