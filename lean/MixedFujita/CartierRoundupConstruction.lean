/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalSNCRoundupVanishing

/-! Construct the rounded Cartier divisor rather than assuming its existence.
The signed coefficients are arbitrary, and the exceptional correction is a
natural number in the projective vanishing interval. -/

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

theorem cartier_roundup_prime_sum_coefficient
    {m : ℕ} (ξ : Fin m → T) (hinj : Function.Injective ξ)
    (G : Fin m → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (b : Fin m → ℤ) (d : ℕ) (t : CodimensionOnePoint T) :
    cartierCoefficient (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) (t : T) =
      ⌈-((cartierCoefficient (∑ i, b i • G i) (t : T) : ℝ) / (d : ℝ))⌉ := by
  by_cases hz : (t : T) ∈ Set.range ξ
  · obtain ⟨i, hi⟩ := hz
    have hg : ∀ a : Fin m → ℤ, cartierCoefficient (∑ j, a j • G j) (t : T) = a i := by
      intro a
      simp only [cartierCoefficient_sum, cartierCoefficient_zsmul, hG]
      simp [← hi, hinj.eq_iff]
    simp only [hg]
  · have hg : ∀ i, (t : T) ≠ ξ i := fun i hi => hz ⟨i, hi.symm⟩
    simp [cartierCoefficient_sum, cartierCoefficient_zsmul, hG, hg]

theorem cartier_roundup_disjoint_sum_coefficient
    {m : ℕ} (ξ : Fin m → T) (hinj : Function.Injective ξ)
    (G : Fin m → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (η : T) (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T,
      cartierCoefficient E (t : T) = if (t : T) = η then 1 else 0)
    (hη : ∀ i, ξ i ≠ η) (b : Fin m → ℤ) (e : ℤ) (d : ℕ)
    (t : CodimensionOnePoint T) :
    cartierCoefficient ((∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) +
        ⌈-((e : ℝ) / (d : ℝ))⌉ • E) (t : T) =
      ⌈-((cartierCoefficient ((∑ i, b i • G i) + e • E) (t : T) : ℝ) / (d : ℝ))⌉ := by
  by_cases ht : (t : T) = η
  · have hg : ∀ i, (t : T) ≠ ξ i := fun i hi => hη i (hi.symm.trans ht)
    simp only [cartierCoefficient_add, cartierCoefficient_sum, cartierCoefficient_zsmul, hG, hE]
    simp only [ite_eq_right (hg _), ite_eq_left ht, mul_zero, Finset.sum_const_zero, zero_add, mul_one]
  · simp only [cartierCoefficient_add, cartierCoefficient_zsmul, hE, ite_eq_right ht,
      mul_zero, add_zero]
    exact cartier_roundup_prime_sum_coefficient ξ hinj G hG b d t

theorem cartier_construct_roundup_totalTransform
    {X : Scheme.{u}} [IsIntegral X] (f : T ⟶ X) [IsDominant f]
    {m : ℕ} (P : Fin m → CartierDivisor X)
    (ξ : Fin m → T) (hinj : Function.Injective ξ) (G : Fin m → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (η : T) (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T,
      cartierCoefficient E (t : T) = if (t : T) = η then 1 else 0)
    (hη : ∀ i, ξ i ≠ η) (s : Finset (Fin m)) (r : ℕ) (hs : s.card ≤ r + 1)
    (hPG : ∀ i, cartierPullback f (P i) = G i + if i ∈ s then E else 0)
    (R : CartierDivisor T) (hR : R = r • E)
    (b : Fin m → ℤ) (d : ℕ) (hd : 1 ≤ d) :
    ∃ (C : CartierDivisor T) (k : ℕ), k ≤ r ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient C (t : T) =
        ⌈-((cartierCoefficient (cartierPullback f (∑ i, b i • P i) - (d : ℤ) • R)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      C = cartierPullback f (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i) + k • E := by
  let e : ℤ := (∑ i ∈ s, b i) - (d : ℤ) * r
  let C := (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) + ⌈-((e : ℝ) / (d : ℝ))⌉ • E
  let k := blowupRoundupCorrection s b d r
  obtain ⟨hk0, hkr⟩ := blowupRoundupCorrection_mem_Icc s b d r hd hs
  have hb : cartierPullback f (∑ i, b i • P i) - (d : ℤ) • R =
      (∑ i, b i • G i) + e • E := by
    rw [cartierPullback_integer_combination,
      totalTransform_sum_decomposition s _ G E hPG, hR]
    dsimp only [e]
    rw [← natCast_zsmul E r, smul_smul, sub_smul]
    abel
  refine ⟨C, k.toNat, by omega, ?_, ?_⟩
  · intro t
    rw [hb]
    exact cartier_roundup_disjoint_sum_coefficient ξ hinj G hG η E hE hη b e d t
  · have hc := roundup_totalTransform_decomposition s (fun i => cartierPullback f (P i))
      G E hPG b d r
    rw [← cartierPullback_integer_combination] at hc
    change C = cartierPullback f (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i) + k • E at hc
    have hk : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    rw [← hk, natCast_zsmul] at hc
    exact hc

end MixedFujita
