/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionLifting
public import MixedFujita.CartierBirationalZeroDivisors

/-! 実固定部分を加えた非零切断・零因子加法と元への降下。 See reports/check-248-high-power-lc-perturbation-complete-base.json for the verified scope. One high residual-power Bertini cut constructs an original effective lc non-klt perturbation klt outside the complete base locus, from one initial nonzero section and a nonempty base. SNC principalization, nonzero fixed part, residual generation, threshold, power and original section descent are internal. A nonempty reduced lower-dimensional non-klt W is internally placed inside that complete base locus without KV. Initial and restricted-section nonvanishing, automatic perturbed adjoint nef-big conditions, usual KV, klt BPF and full F1/F2 remain unproved. -/

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
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra




/-- Adding the effective fixed part to an actual residual section preserves its
rational function and adds that fixed part to its actual effective zero divisor. -/
theorem exists_cartier_section_add_fixed_part
    {T : Scheme.{u}} [IsIntegral T] (M F : CartierDivisor T) (hF : F.IsEffective)
    (s : Γ((M - F).sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ (t : Γ(M.sheaf, ⊤)) (ht : t ≠ 0),
      cartierSectionZeroDivisor M t ht = F + cartierSectionZeroDivisor (M - F) s hs := by
  let j := cartierEffectiveInclusion M F hF
  let t := Scheme.Modules.Hom.app j ⊤ s
  have he : cartierSectionRational M t = cartierSectionRational (M - F) s := by
    apply congrArg (rationalFunctionsEquiv (X := T) ⊤)
      (ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤)
        (cartierEffectiveInclusion_ι M F hF)) s)
  have ht : t ≠ 0 := by
    intro h
    have hz : cartierSectionRational (M - F) s = 0 := by rw [← he, h, map_zero]
    exact hs (cartierSectionRational_injective (M - F) (hz.trans (map_zero _).symm))
  have hu : cartierSectionUnit M t ht = cartierSectionUnit (M - F) s hs := Units.ext he
  refine ⟨t, ht, ?_⟩
  rw [cartierSectionZeroDivisor, hu, cartierSectionZeroDivisor]
  abel


/-- A residual section on a proper birational model descends to an ORIGINAL
section after adjoining its effective fixed part, with exact zero-divisor identity. -/
theorem proper_birational_exists_fixed_part_section_descent
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X]
    (p : T ⟶ X) [IsDominant p] [IsProper p]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hp : Function.Surjective (dominantFunctionFieldMap p).hom)
    (M : CartierDivisor X) (F : CartierDivisor T) (hF : F.IsEffective)
    (s : Γ((cartierPullback p M - F).sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ (t : Γ(M.sheaf, ⊤)) (ht : t ≠ 0),
      cartierPullback p (cartierSectionZeroDivisor M t ht) =
        F + cartierSectionZeroDivisor (cartierPullback p M - F) s hs := by
  obtain ⟨u, hu, hzero⟩ := exists_cartier_section_add_fixed_part (cartierPullback p M) F hF s hs
  obtain ⟨t, ht, _, he⟩ := proper_birational_exists_section_zeroDivisor_descent p hnorm hp M u hu
  exact ⟨t, ht, he.trans hzero⟩

end MixedFujita
