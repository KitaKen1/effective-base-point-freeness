/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalSubcutUnitInclusion
public import MixedFujita.NormalCartierBaseNeighborhoodSections
public import MixedFujita.BirationalPrimeLifts

/-! 元一般点近傍の双有理Cartier単位と標準kernel包含の非零性。 See reports/check-245-lc-kernel-closed-subscheme-lifting.json for the verified scope. The canonical lc kernel gives a proper nonzero actual image ideal, a concrete nonzero untwisted quotient unit, and a nonempty lower-dimensional actual closed subscheme W. Usual KV gives actual Cartier restriction section lifting to W. Usual KV itself and nonzero/generating sections of P restricted to W remain unproved; W is not identified with a reduced lc center; klt BPF and full F1/F2 remain incomplete. -/

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


/-- A birational map has no codimension-one point above the original generic point.
The actual stalk map is bijective over the generic valuation field. -/
theorem birational_prime_not_over_genericPoint
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (p : T ⟶ X) [IsDominant p]
    (hp : Function.Bijective (dominantFunctionFieldMap p).hom) (t : CodimensionOnePoint T) :
    p (t : T) ≠ genericPoint X := by
  intro ht
  let : ValuationRing (X.presheaf.stalk (p (t : T))) := by
    rw [ht]
    change ValuationRing X.functionField
    infer_instance
  have hb := stalkMap_bijective_of_birational_valuation_stalk p hp (t : T)
  have hc := coheight_eq_of_stalkMap_bijective p (t : T) hb
  rw [ht, coheight_genericPoint_eq_zero, t.property] at hc
  exact one_ne_zero hc


/-- Every Cartier lattice on a normal noetherian birational source contains the unit
over some ACTUAL neighbourhood of the ORIGINAL generic point. No properness is needed. -/
theorem birational_cartier_unit_section_near_original_genericPoint
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    (p : T ⟶ X) [IsDominant p]
    (hp : Function.Bijective (dominantFunctionFieldMap p).hom)
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t)) (C : CartierDivisor T) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧
      Scheme.Modules.Hom.app (toRationalFunctions T) (p ⁻¹ᵁ U) (1 : Γ(T, p ⁻¹ᵁ U)) ∈
        C.sections (p ⁻¹ᵁ U) := by
  apply (exists_base_neighborhood_one_mem_cartier_sections_iff hnormT p (genericPoint X) C).mpr
  intro t ht
  have he : p (t : T) = genericPoint X :=
    ((specializes_iff_mem_closure.mpr ht).antisymm (genericPoint_specializes _)).eq
  exact False.elim (birational_prime_not_over_genericPoint p hp t he)


/-- The canonical birational subcut map is nonzero because its image contains the
unit on some actual generic neighbourhood, even when it contains no global unit. -/
theorem cartierSubcutPushforwardUnitInclusion_ne_zero
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    (p : T ⟶ X) [IsDominant p]
    (hp : Function.Bijective (dominantFunctionFieldMap p).hom)
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)] :
    cartierSubcutPushforwardUnitInclusion p E S hE hS ≠ 0 := by
  obtain ⟨U, hU, hs⟩ := birational_cartier_unit_section_near_original_genericPoint p hp hnormT (E - S)
  obtain ⟨s, hs⟩ := (one_in_range_cartierSubcutPushforwardUnitInclusion_iff p E S hE hS U).mpr hs
  let : Nonempty U := ⟨⟨genericPoint X, hU⟩⟩
  intro hz
  rw [hz] at hs
  change (0 : Γ(X, U)) = 1 at hs
  exact zero_ne_one hs

end MixedFujita
