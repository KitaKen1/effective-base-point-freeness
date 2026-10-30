/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierRoundupConstruction

/-! Simultaneous rounding with component-dependent exceptional discrepancies.
The geometric prime profiles, total transforms and canonical expression are
explicit inputs. Neither equal discrepancies nor a connected centre is needed.
The rounded divisor and all bounded natural correction coefficients are outputs. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

theorem multiple_totalTransform_sum_decomposition
    {M : Type*} [AddCommGroup M] {m : ℕ} {J : Type*} [Fintype J]
    (s : J → Finset (Fin m)) (F G : Fin m → M) (E : J → M)
    (hFG : ∀ i, F i = G i + ∑ j, if i ∈ s j then E j else 0)
    (a : Fin m → ℤ) :
    ∑ i, a i • F i = (∑ i, a i • G i) + ∑ j, (∑ i ∈ s j, a i) • E j := by
  classical
  simp_rw [hFG, smul_add, Finset.smul_sum]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [smul_ite, Finset.sum_ite_mem, Finset.sum_smul]

theorem multiple_roundup_totalTransform_decomposition
    {M : Type*} [AddCommGroup M] {m : ℕ} {J : Type*} [Fintype J]
    (s : J → Finset (Fin m)) (F G : Fin m → M) (E : J → M)
    (hFG : ∀ i, F i = G i + ∑ j, if i ∈ s j then E j else 0)
    (b : Fin m → ℤ) (d : ℕ) (r : J → ℕ) :
    (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) +
        ∑ j, ⌈-((((∑ i ∈ s j, b i) - (d : ℤ) * r j : ℤ) : ℝ) / (d : ℝ))⌉ • E j =
      (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • F i) +
        ∑ j, blowupRoundupCorrection (s j) b d (r j) • E j := by
  rw [multiple_totalTransform_sum_decomposition s F G E hFG]
  simp_rw [blowupRoundupCorrection, sub_smul]
  rw [Finset.sum_sub_distrib]
  abel

variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]

theorem cartier_roundup_fintype_prime_sum_coefficient
    {I : Type*} [Fintype I] (ξ : I → T) (hinj : Function.Injective ξ)
    (G : I → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (b : I → ℤ) (d : ℕ) (t : CodimensionOnePoint T) :
    cartierCoefficient (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) (t : T) =
      ⌈-((cartierCoefficient (∑ i, b i • G i) (t : T) : ℝ) / (d : ℝ))⌉ := by
  classical
  by_cases hz : (t : T) ∈ Set.range ξ
  · obtain ⟨i, hi⟩ := hz
    have hg : ∀ a : I → ℤ, cartierCoefficient (∑ j, a j • G j) (t : T) = a i := by
      intro a
      simp only [cartierCoefficient_sum, cartierCoefficient_zsmul, hG]
      simp [← hi, hinj.eq_iff]
    simp only [hg]
  · have hg : ∀ i, (t : T) ≠ ξ i := fun i hi => hz ⟨i, hi.symm⟩
    simp [cartierCoefficient_sum, cartierCoefficient_zsmul, hG, hg]

theorem cartier_roundup_two_prime_families_coefficient
    {I J : Type*} [Fintype I] [Fintype J]
    (ξ : I → T) (hinj : Function.Injective ξ) (G : I → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (η : J → T) (hηinj : Function.Injective η) (E : J → CartierDivisor T)
    (hE : ∀ j (t : CodimensionOnePoint T),
      cartierCoefficient (E j) (t : T) = if (t : T) = η j then 1 else 0)
    (hdis : ∀ i j, ξ i ≠ η j) (b : I → ℤ) (e : J → ℤ) (d : ℕ)
    (t : CodimensionOnePoint T) :
    cartierCoefficient ((∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • G i) +
        ∑ j, ⌈-((e j : ℝ) / (d : ℝ))⌉ • E j) (t : T) =
      ⌈-((cartierCoefficient ((∑ i, b i • G i) + ∑ j, e j • E j) (t : T) : ℝ) /
        (d : ℝ))⌉ := by
  classical
  by_cases hz : (t : T) ∈ Set.range η
  · obtain ⟨j, hj⟩ := hz
    have hg : ∀ i, (t : T) ≠ ξ i := fun i hi => hdis i j (hi.symm.trans hj.symm)
    simp only [cartierCoefficient_add, cartierCoefficient_sum, cartierCoefficient_zsmul,
      hG, ite_eq_right (hg _), mul_zero, Finset.sum_const_zero, zero_add]
    simpa only [cartierCoefficient_sum, cartierCoefficient_zsmul] using
      cartier_roundup_fintype_prime_sum_coefficient η hηinj E hE e d t
  · have he : ∀ j, (t : T) ≠ η j := fun j hj => hz ⟨j, hj.symm⟩
    simp only [cartierCoefficient_add, cartierCoefficient_sum, cartierCoefficient_zsmul,
      hE, ite_eq_right (he _), mul_zero, Finset.sum_const_zero, add_zero]
    simpa only [cartierCoefficient_sum, cartierCoefficient_zsmul] using
      cartier_roundup_fintype_prime_sum_coefficient ξ hinj G hG b d t

/-- Construct the intrinsic rounded divisor and a separate correction in
`[0,r j]` for each exceptional prime, from the displayed geometric identities. -/
theorem cartier_construct_roundup_multiple_totalTransform
    {X : Scheme.{u}} [IsIntegral X] (f : T ⟶ X) [IsDominant f]
    {m : ℕ} {J : Type*} [Fintype J] (P : Fin m → CartierDivisor X)
    (ξ : Fin m → T) (hinj : Function.Injective ξ) (G : Fin m → CartierDivisor T)
    (hG : ∀ i (t : CodimensionOnePoint T),
      cartierCoefficient (G i) (t : T) = if (t : T) = ξ i then 1 else 0)
    (η : J → T) (hηinj : Function.Injective η) (E : J → CartierDivisor T)
    (hE : ∀ j (t : CodimensionOnePoint T),
      cartierCoefficient (E j) (t : T) = if (t : T) = η j then 1 else 0)
    (hdis : ∀ i j, ξ i ≠ η j) (s : J → Finset (Fin m)) (r : J → ℕ)
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
    exact cartier_roundup_two_prime_families_coefficient ξ hinj G hG η hηinj E hE hdis b e d t
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
