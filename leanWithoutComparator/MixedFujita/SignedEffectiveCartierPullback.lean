/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierPullbackUntwist
public import MixedFujita.SNCBoundaryRoundup
public import MixedFujita.NormalEffectiveCartierPrime

/-! Signed combinations of effective Cartier divisors have an actual
divisor/module pullback comparison without an ample class or a global section
of the signed divisor. Split the coefficients into positive and negative
parts, then cancel the two effective pullback comparisons. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem signed_effective_cartier_sum_exists_difference
    {X : Scheme.{u}} [IsIntegral X] {ι : Type*} [Fintype ι]
    (P : ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective) (a : ι → ℤ) :
    ∃ A B : CartierDivisor X, A.IsEffective ∧ B.IsEffective ∧
      (∑ i, a i • P i) = A - B := by
  classical
  have heff (b : ι → ℤ) (hb : ∀ i, 0 ≤ b i) : (∑ i, b i • P i).IsEffective := by
    apply Finset.sum_induction _ CartierDivisor.IsEffective (fun _ _ h1 h2 ↦ h1.add h2)
      CartierDivisor.isEffective_zero
    intro i _
    exact cartierIsEffective_zsmul_nonneg (P i) (hP i) (b i) (hb i)
  refine ⟨∑ i, max (a i) 0 • P i, ∑ i, max (-a i) 0 • P i,
    heff _ (fun i ↦ le_max_right _ _), heff _ (fun i ↦ le_max_right _ _), ?_⟩
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_smul]
  congr 1
  omega

theorem cartierPullback_moduleIso_of_effective_difference
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (ρ : T ⟶ X) [IsDominant ρ] (D A B : CartierDivisor X)
    (hA : A.IsEffective) (hB : B.IsEffective) (hD : D = A - B) :
    Nonempty ((Scheme.Modules.pullback ρ).obj D.sheaf ≅ (cartierPullback ρ D).sheaf) := by
  subst D
  exact ⟨cartierPullbackSubIso A B ρ (cartierPullback ρ A) (cartierPullback ρ B)
    (effectiveCartierPullbackModuleIso ρ A hA) (effectiveCartierPullbackModuleIso ρ B hB) ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (cartierPullback_sub ρ A B).symm)⟩

theorem signed_exceptional_combination_exists_effective_difference
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (π : T ⟶ X) [IsDominant π] {ι : Type*} [Fintype ι]
    (P : ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective) (a : ι → ℤ)
    (E : CartierDivisor T) (hE : E.IsEffective) (j : ℕ)
    (C : CartierDivisor T) (hC : C = cartierPullback π (∑ i, a i • P i) + j • E) :
    ∃ A B : CartierDivisor T, A.IsEffective ∧ B.IsEffective ∧ C = A - B := by
  obtain ⟨A, B, hA, hB, hAB⟩ := signed_effective_cartier_sum_exists_difference P hP a
  have hjE : (j • E).IsEffective := by
    simpa only [natCast_zsmul] using
      cartierIsEffective_zsmul_nonneg E hE (j : ℤ) (by omega)
  refine ⟨cartierPullback π A + j • E, cartierPullback π B,
    (cartierPullback_effective_of_effective π A hA).add hjE,
    cartierPullback_effective_of_effective π B hB, ?_⟩
  rw [hC, hAB, cartierPullback_sub]
  abel

theorem signed_exceptional_combination_pullback_moduleIso
    {X T Y : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsIntegral Y]
    (π : T ⟶ X) [IsDominant π] (τ : Y ⟶ T) [IsDominant τ]
    {ι : Type*} [Fintype ι] (P : ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (a : ι → ℤ) (E : CartierDivisor T) (hE : E.IsEffective) (j : ℕ)
    (C : CartierDivisor T) (hC : C = cartierPullback π (∑ i, a i • P i) + j • E) :
    Nonempty ((Scheme.Modules.pullback τ).obj C.sheaf ≅ (cartierPullback τ C).sheaf) := by
  obtain ⟨A, B, hA, hB, hAB⟩ :=
    signed_exceptional_combination_exists_effective_difference π P hP a E hE j C hC
  exact cartierPullback_moduleIso_of_effective_difference τ C A B hA hB hAB

end MixedFujita
