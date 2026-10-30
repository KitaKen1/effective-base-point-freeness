/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.NormalEffectiveCartierPrime
public import MixedFujita.NormalCartierLocalUnits

/-!
On a normal integral Noetherian scheme, a nonunit effective Cartier equation
has a positive prime component through its point. The finite Weil support and
two-sided Hartogs construct the prime without assuming an SNC model or a
supplied prime witness. This local support statement works in every characteristic.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]

/-- Outside the finite closed prime support, every regular local Cartier equation is a unit. -/
theorem normal_nonunit_localEquation_mem_cartierSupportCloseds
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : CartierDivisor X) (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (hnonunit : ¬ IsUnit a) : x ∈ (cartierSupportCloseds D : Set X) := by
  classical
  by_contra hx
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  let W : X.Opens := V ⊓ (cartierSupportCloseds D).compl
  have hxW : x ∈ W := ⟨hxV, hx⟩
  letI : ∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    fun z => by
      letI := hnorm (z : X)
      exact normal_codimensionOne_stalk_DVR z
  obtain ⟨u, hu⟩ := normal_scheme_ord_zero_exists_stalk_unit hnorm x W hxW f (by
    intro z hz
    have hfz := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV hz.1
    rw [← cartierCoefficient_eq_ord hfz]
    exact cartierCoefficient_eq_zero_of_notMem_cartierSupportCloseds D (z : X) z.property hz.2)
  have heq : a = (u : X.presheaf.stalk x) :=
    (IsFractionRing.injective (X.presheaf.stalk x) X.functionField) (ha.trans hu.symm)
  apply hnonunit
  rw [heq]
  exact u.isUnit

/-- A nonunit effective Cartier equation supplies an actual positive component through its point. -/
theorem normal_effective_exists_positive_coefficient_through_point
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : CartierDivisor X) (hD : D.IsEffective) (x : X)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (a : X.presheaf.stalk x)
    (ha : algebraMap (X.presheaf.stalk x) X.functionField a = (f : X.functionField))
    (hnonunit : ¬ IsUnit a) :
    ∃ z : CodimensionOnePoint X, x ∈ closure ({(z : X)} : Set X) ∧
      0 < cartierCoefficient D (z : X) := by
  have hs := normal_nonunit_localEquation_mem_cartierSupportCloseds hnorm D x f hf a ha hnonunit
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hs
  have hne : cartierCoefficient D (z : X) ≠ 0 := by
    rw [← cartier_toWeilDivisor_coeff_eq_cartierCoefficient D z]
    exact Finsupp.mem_support_iff.mp hz
  have hnonneg := cartierCoefficient_nonneg_of_isEffective D hD (z : X)
  exact ⟨z, hxz, by omega⟩

end MixedFujita
