/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.CartierSectionSNCPerturbation
public import MixedFujita.SNCBoundaryDiscrepancy

/-! A generization of a prime divisor on an integral scheme is that point or
the generic point. Test primes mapping to the generic point see zero order
of every effective Cartier base divisor. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- There are exactly two possible generizations of a codimension-one point on an integral scheme. -/
theorem eq_or_eq_genericPoint_of_specializes_to_base_prime
    {Y : Scheme.{u}} [IsIntegral Y] (η : Y) (hη : Order.coheight η = 1)
    (y : Y) (hy : η ∈ closure ({y} : Set Y)) : y = η ∨ y = genericPoint Y := by
  by_cases heq : y = η
  · exact Or.inl heq
  · right
    have hle : η ≤ y := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hy)
    have hgt : η < y := lt_iff_le_not_ge.mpr ⟨hle, fun h =>
      heq ((Scheme.le_iff_specializes.mp hle).antisymm (Scheme.le_iff_specializes.mp h)).eq⟩
    have hfin : Order.coheight y < ⊤ := lt_of_le_of_lt (Order.coheight_anti hle)
      (by rw [hη]; exact ENat.coe_lt_top 1)
    have hlt := Order.coheight_strictAnti hgt hfin
    rw [hη] at hlt
    have hzero : Order.coheight y = 0 := by simpa only [ENat.lt_one_iff_eq_zero] using hlt
    have hmax := Order.coheight_eq_zero.mp hzero
    have hgeneric : y ≤ genericPoint Y := Scheme.le_iff_specializes.mpr
      ((genericPoint_spec Y).specializes (Set.mem_univ y))
    exact ((Scheme.le_iff_specializes.mp (hmax hgeneric)).antisymm
      (Scheme.le_iff_specializes.mp hgeneric)).eq

/-- An effective Cartier base divisor has zero pullback coefficient at a test point mapping generically. -/
theorem cartierPullback_coefficient_eq_zero_of_image_genericPoint
    {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y] [IsLocallyNoetherian T]
    [IsLocallyNoetherian Y] (q : T ⟶ Y) [IsDominant q]
    (H : CartierDivisor Y) (hH : H.IsEffective) (t : T) (ht : q t = genericPoint Y) :
    cartierCoefficient (cartierPullback q H) t = 0 := by
  obtain ⟨f, hf, a, ha⟩ := CartierDivisor.isEffective_iff_exists.mp hH (q t)
  have hfield : IsField (Y.presheaf.stalk (q t)) := by
    rw [ht]
    exact Field.toIsField Y.functionField
  letI := hfield.toField
  have ha0 : a ≠ 0 := by
    intro hz
    have h := Units.ne_zero f
    apply h
    rw [← ha, hz, map_zero]
  have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha0
  have hmap : (dominantFunctionFieldMap q).hom (f : Y.functionField) =
      algebraMap (T.presheaf.stalk t) T.functionField ((q.stalkMap t).hom a) := by
    rw [← dominantFunctionFieldMap_algebraMap, ha]
  rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt q H t hf)]
  change T.ord ((dominantFunctionFieldMap q).hom (f : Y.functionField)) t = 0
  rw [hmap]
  exact scheme_ord_stalk_unit t ((hu.map (q.stalkMap t).hom).unit)

end MixedFujita
