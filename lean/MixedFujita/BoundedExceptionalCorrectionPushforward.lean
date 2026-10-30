/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ComponentExceptionalModulePullback
public import MixedFujita.ExceptionalCartierProjectionFormula
public import MixedFujita.CoordinateBlowupStalkCanonical
public import MixedFujita.NormalBirationalPrimeLifts

/-! A bounded effective correction is exceptional whenever its upper bound
is exceptional. Applied to the actual relative canonical divisor, this
constructs the zero-degree direct image of the signed rounded Cartier sheaf. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem bounded_effective_correction_coefficient_zero
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] {J : Type*} [Fintype J]
    (E : J → CartierDivisor T) (hE : ∀ i, (E i).IsEffective)
    (r j : J → ℕ) (hj : ∀ i, j i ≤ r i) (t : T)
    (hr : cartierCoefficient (∑ i, r i • E i) t = 0) :
    cartierCoefficient (∑ i, j i • E i) t = 0 := by
  have hnon := cartierCoefficient_nonneg_of_isEffective _
    (component_exceptional_correction_isEffective E hE j) t
  have hle : cartierCoefficient (∑ i, j i • E i) t ≤
      cartierCoefficient (∑ i, r i • E i) t := by
    simp only [cartierCoefficient_sum, cartierCoefficient_nsmul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj i)
      (cartierCoefficient_nonneg_of_isEffective _ (hE i) t)
  omega

theorem relativeCanonical_coefficient_zero_over_normal_prime
    {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {n : ℕ}
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (cT₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ cT₀))
    (t : CodimensionOnePoint T) (ht : Order.coheight (ρ (t : T)) = 1) :
    cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX cT₀ hT hR) (t : T) = 0 := by
  let := hnormT (t : T)
  let := normal_codimensionOne_stalk_DVR t
  exact relativeCanonical_coefficient_zero_of_stalkMap_bijective ρ c₀ hX cT₀ hT hR t
    (stalkMap_bijective_of_birational_over_normal_prime hnormX ρ hρ (t : T) ht)

theorem signed_bounded_exceptional_correction_pushforward_iso
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    {ι J : Type*} [Fintype ι] [Fintype J]
    (P : ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective) (a : ι → ℤ)
    (E : J → CartierDivisor T) (hE : ∀ i, (E i).IsEffective)
    (r j : J → ℕ) (hj : ∀ i, j i ≤ r i)
    (hr : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient (∑ i, r i • E i) (t : T) = 0)
    (C : CartierDivisor T)
    (hC : C = cartierPullback ρ (∑ i, a i • P i) + ∑ i, j i • E i) :
    Nonempty ((∑ i, a i • P i).sheaf ≅ (Scheme.Modules.pushforward ρ).obj C.sheaf) := by
  let F := ∑ i, j i • E i
  have hF : F.IsEffective := component_exceptional_correction_isEffective E hE j
  have hEx : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient F (t : T) = 0 := by
    intro t ht
    exact bounded_effective_correction_coefficient_zero E hE r j hj _ (hr t ht)
  obtain ⟨A, B, hA, hB, hAB⟩ := signed_effective_cartier_sum_exists_difference P hP a
  obtain ⟨e⟩ := cartierPullback_moduleIso_of_effective_difference ρ _ A B hA hB hAB
  exact ⟨effectiveExceptionalCartierTwistedPushforwardIso hnormX hnormT ρ hρ F hF hEx _ ≪≫
    (Scheme.Modules.pushforward ρ).mapIso
      (tensorIso e (Iso.refl _) ≪≫ cartierTensorSheafIso _ F ≪≫
        eqToIso (congrArg CartierDivisor.sheaf hC.symm))⟩

end MixedFujita
