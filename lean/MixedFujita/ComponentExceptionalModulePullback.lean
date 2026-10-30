/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SignedEffectiveCartierPullback
public import MixedFujita.ComponentExceptionalLocalization

/-! Ordinary module pullback for a signed boundary with a finite effective
exceptional correction. Splitting the signed boundary once avoids any
ampleness or global generation requirement on the rounded divisor. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem component_exceptional_correction_isEffective
    {T : Scheme.{u}} [IsIntegral T] {J : Type*} [Fintype J]
    (E : J → CartierDivisor T) (hE : ∀ i, (E i).IsEffective) (j : J → ℕ) :
    (∑ i, j i • E i).IsEffective := by
  apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 ↦ h1.add h2)
    CartierDivisor.isEffective_zero
  intro i _
  simpa only [natCast_zsmul] using
    cartierIsEffective_zsmul_nonneg (E i) (hE i) (j i : ℤ) (by omega)

theorem component_exceptional_combination_exists_effective_difference
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (π : T ⟶ X) [IsDominant π] {ι J : Type*} [Fintype ι] [Fintype J]
    (P : ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective) (a : ι → ℤ)
    (E : J → CartierDivisor T) (hE : ∀ i, (E i).IsEffective) (j : J → ℕ)
    (C : CartierDivisor T)
    (hC : C = cartierPullback π (∑ i, a i • P i) + ∑ i, j i • E i) :
    ∃ A B : CartierDivisor T, A.IsEffective ∧ B.IsEffective ∧ C = A - B := by
  apply signed_exceptional_combination_exists_effective_difference π P hP a
    (∑ i, j i • E i) (component_exceptional_correction_isEffective E hE j) 1 C
  simpa only [one_smul] using hC

theorem component_exceptional_combination_pullback_moduleIso
    {X T Y : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsIntegral Y]
    (π : T ⟶ X) [IsDominant π] (τ : Y ⟶ T) [IsDominant τ]
    {ι J : Type*} [Fintype ι] [Fintype J]
    (P : ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective) (a : ι → ℤ)
    (E : J → CartierDivisor T) (hE : ∀ i, (E i).IsEffective) (j : J → ℕ)
    (C : CartierDivisor T)
    (hC : C = cartierPullback π (∑ i, a i • P i) + ∑ i, j i • E i) :
    Nonempty ((Scheme.Modules.pullback τ).obj C.sheaf ≅ (cartierPullback τ C).sheaf) := by
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    component_exceptional_combination_exists_effective_difference π P hP a E hE j C hC
  exact cartierPullback_moduleIso_of_effective_difference τ C A B hA hB hAB

end MixedFujita
