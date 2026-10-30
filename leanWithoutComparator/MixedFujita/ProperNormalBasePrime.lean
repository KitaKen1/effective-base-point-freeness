/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalEffectivePrimeThroughPoint
public import MixedFujita.ProperSNCPositiveBaseCoefficient

/-!
A proper dominant map from a normal Noetherian scheme supplies a positive
prime component of an effective Cartier pullback over a base point where its
equation is a nonunit. No SNC structure or positive prime witness is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsIntegral Y]
  (g : X ⟶ Y) [IsDominant g] [IsProper g]

/-- A nonunit equation at the base supplies an actual positive prime upstairs. -/
theorem proper_normal_pullback_exists_positive_prime_over_point
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (H : CartierDivisor Y) (hH : H.IsEffective) (η : Y)
    (f : Y.functionFieldˣ) (hf : H.IsLocalEquationAt η f)
    (a : Y.presheaf.stalk η)
    (ha : algebraMap (Y.presheaf.stalk η) Y.functionField a = (f : Y.functionField))
    (hnonunit : ¬ IsUnit a) :
    ∃ z : CodimensionOnePoint X, η ∈ closure ({g (z : X)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback g H) (z : X) := by
  obtain ⟨p, rfl⟩ := surjective_of_isProper_of_isDominant g η
  have hmap : algebraMap (X.presheaf.stalk p) X.functionField (g.stalkMap p a) =
      ((Units.map (dominantFunctionFieldMap g).hom.toMonoidHom f : X.functionFieldˣ) :
        X.functionField) := by
    rw [← dominantFunctionFieldMap_algebraMap g p a, ha]
    rfl
  have hnu : ¬ IsUnit (g.stalkMap p a) := by
    intro hu
    exact hnonunit (IsLocalHom.map_nonunit (f := (g.stalkMap p).hom) a hu)
  obtain ⟨z, hz, hpos⟩ := normal_effective_exists_positive_coefficient_through_point hnorm
    (cartierPullback g H) (cartierPullback_effective_of_effective g H hH) p
    (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom f)
    (cartierPullback_isLocalEquationAt g H p hf) (g.stalkMap p a) hmap hnu
  exact ⟨z, specializes_iff_mem_closure.mp
    ((specializes_iff_mem_closure.mpr hz).map g.continuous), hpos⟩

/-- Positive order at a base prime internally supplies the required nonunit. -/
theorem proper_normal_pullback_exists_positive_prime_over_base_prime [IsLocallyNoetherian Y]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (H : CartierDivisor Y) (hH : H.IsEffective) (η : CodimensionOnePoint Y)
    (hη : 0 < cartierCoefficient H (η : Y)) :
    ∃ z : CodimensionOnePoint X, (η : Y) ∈ closure ({g (z : X)} : Set Y) ∧
      0 < cartierCoefficient (cartierPullback g H) (z : X) := by
  obtain ⟨f, hf, a, ha⟩ := CartierDivisor.isEffective_iff_exists.mp hH (η : Y)
  have hnonunit : ¬ IsUnit a := by
    intro hu
    have hz : cartierCoefficient H (η : Y) = 0 := by
      rw [cartierCoefficient_eq_ord hf, ← ha]
      exact scheme_ord_stalk_unit (η : Y) hu.unit
    omega
  exact proper_normal_pullback_exists_positive_prime_over_point g hnorm H hH (η : Y)
    f hf a ha hnonunit

end MixedFujita
