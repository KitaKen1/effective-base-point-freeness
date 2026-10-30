/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MultipleExceptionalRoundup

/-! Rounding using disjoint support profiles. An exceptional divisor may have
more than one prime component: uniqueness of the active support at each
codimension-one point suffices, without selecting exceptional generic points. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable
variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]

theorem cartier_roundup_support_sum_coefficient
    {J : Type*} [Fintype J] (S : J → Set T)
    (hS : ∀ (t : CodimensionOnePoint T) i j, (t : T) ∈ S i → (t : T) ∈ S j → i = j)
    (E : J → CartierDivisor T)
    (hE : ∀ j (t : CodimensionOnePoint T),
      cartierCoefficient (E j) (t : T) = if (t : T) ∈ S j then 1 else 0)
    (b : J → ℤ) (d : ℕ) (t : CodimensionOnePoint T) :
    cartierCoefficient (∑ j, ⌈-((b j : ℝ) / (d : ℝ))⌉ • E j) (t : T) =
      ⌈-((cartierCoefficient (∑ j, b j • E j) (t : T) : ℝ) / (d : ℝ))⌉ := by
  classical
  by_cases ht : ∃ j, (t : T) ∈ S j
  · obtain ⟨j, hj⟩ := ht
    have he : ∀ i, (t : T) ∈ S i ↔ i = j := by
      intro i
      exact ⟨fun hi => hS t i j hi hj, fun h => h ▸ hj⟩
    have hcoef : ∀ a : J → ℤ, cartierCoefficient (∑ i, a i • E i) (t : T) = a j := by
      intro a
      simp [cartierCoefficient_sum, cartierCoefficient_zsmul, hE, he]
    simp only [hcoef]
  · have he : ∀ i, (t : T) ∉ S i := fun i hi => ht ⟨i, hi⟩
    simp [cartierCoefficient_sum, cartierCoefficient_zsmul, hE, he]

theorem cartier_roundup_prime_and_support_families_coefficient
    {I J : Type*} [Fintype I] [Fintype J]
    (ξ : I → T) (hinj : Function.Injective ξ) (G : I → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (S : J → Set T)
    (hS : ∀ (t : CodimensionOnePoint T) i j, (t : T) ∈ S i → (t : T) ∈ S j → i = j)
    (E : J → CartierDivisor T)
    (hE : ∀ j (t : CodimensionOnePoint T),
      cartierCoefficient (E j) (t : T) = if (t : T) ∈ S j then 1 else 0)
    (hdis : ∀ i j, ξ i ∉ S j) (b : I → ℤ) (e : J → ℤ) (d : ℕ)
    (t : CodimensionOnePoint T) :
    cartierCoefficient ((∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) +
        ∑ j, ⌈-((e j : ℝ) / (d : ℝ))⌉ • E j) (t : T) =
      ⌈-((cartierCoefficient ((∑ i, b i • G i) + ∑ j, e j • E j) (t : T) : ℝ) /
        (d : ℝ))⌉ := by
  classical
  by_cases ht : ∃ j, (t : T) ∈ S j
  · obtain ⟨j, hj⟩ := ht
    have hg : ∀ i, (t : T) ≠ ξ i := fun i hi => hdis i j (hi ▸ hj)
    simp only [cartierCoefficient_add, cartierCoefficient_sum, cartierCoefficient_zsmul,
      hG, ite_eq_right (hg _), mul_zero, Finset.sum_const_zero, zero_add]
    simpa only [cartierCoefficient_sum, cartierCoefficient_zsmul] using
      cartier_roundup_support_sum_coefficient S hS E hE e d t
  · have he : ∀ j, (t : T) ∉ S j := fun j hj => ht ⟨j, hj⟩
    simp only [cartierCoefficient_add, cartierCoefficient_sum, cartierCoefficient_zsmul,
      hE, ite_eq_right (he _), mul_zero, Finset.sum_const_zero, add_zero]
    simpa only [cartierCoefficient_sum, cartierCoefficient_zsmul] using
      cartier_roundup_fintype_prime_sum_coefficient ξ hinj G hG b d t

theorem cartier_construct_roundup_disjoint_support_totalTransform
    {X : Scheme.{u}} [IsIntegral X] (f : T ⟶ X) [IsDominant f]
    {m : ℕ} {J : Type*} [Fintype J] (P : Fin m → CartierDivisor X)
    (ξ : Fin m → T) (hinj : Function.Injective ξ) (G : Fin m → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (S : J → Set T)
    (hS : ∀ (t : CodimensionOnePoint T) i j, (t : T) ∈ S i → (t : T) ∈ S j → i = j)
    (E : J → CartierDivisor T)
    (hE : ∀ j (t : CodimensionOnePoint T),
      cartierCoefficient (E j) (t : T) = if (t : T) ∈ S j then 1 else 0)
    (hdis : ∀ i j, ξ i ∉ S j) (s : J → Finset (Fin m)) (r : J → ℕ)
    (hs : ∀ j, (s j).card ≤ r j + 1)
    (hPG : ∀ i, cartierPullback f (P i) = G i + ∑ j, if i ∈ s j then E j else 0)
    (R : CartierDivisor T) (hR : R = ∑ j, r j • E j)
    (b : Fin m → ℤ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (C : CartierDivisor T) (k : J → ℕ), (∀ j, k j ≤ r j) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
        ⌈-((cartierCoefficient (cartierPullback f (∑ i, b i • P i) - (d : ℤ) • R)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      C = cartierPullback f (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i) + ∑ j, k j • E j := by
  classical
  let e : J → ℤ := fun j => (∑ i ∈ s j, b i) - (d : ℤ) * r j
  let C := (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) +
    ∑ j, ⌈-((e j : ℝ) / (d : ℝ))⌉ • E j
  let k : J → ℤ := fun j => blowupRoundupCorrection (s j) b d (r j)
  have hk : ∀ j, 0 ≤ k j ∧ k j ≤ r j := fun j =>
    blowupRoundupCorrection_mem_Icc (s j) b d (r j) hd (hs j)
  have hb : cartierPullback f (∑ i, b i • P i) - (d : ℤ) • R =
      (∑ i, b i • G i) + ∑ j, e j • E j := by
    rw [cartierPullback_integer_combination,
      multiple_totalTransform_sum_decomposition s _ G E hPG, hR]
    dsimp only [e]
    simp_rw [Finset.smul_sum, ← natCast_zsmul (E _) (r _), smul_smul, sub_smul]
    rw [Finset.sum_sub_distrib]
    abel
  refine ⟨C, fun j => (k j).toNat, fun j => Int.toNat_le.mpr (hk j).2, ?_, ?_⟩
  · intro t
    rw [hb]
    exact cartier_roundup_prime_and_support_families_coefficient ξ hinj G hG S hS E hE hdis b e d t
  · have hc := multiple_roundup_totalTransform_decomposition s
      (fun i => cartierPullback f (P i)) G E hPG b d r
    rw [← cartierPullback_integer_combination] at hc
    change C = cartierPullback f (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i) + ∑ j, k j • E j at hc
    rw [hc]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [← natCast_zsmul, Int.toNat_of_nonneg (hk j).1]

end MixedFujita
