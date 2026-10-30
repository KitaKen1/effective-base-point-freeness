/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalBasePrimeUniformizer
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-!
On an actual affine normal base, a DVR uniformizer is a fraction of global
sections. Its denominator is a local unit, so its numerator has irreducible
germ too. The resulting global principal effective Cartier divisor has
coefficient one at the chosen prime. No global uniformizer is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsAffine Y]
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]

/-- A global regular numerator is itself a local uniformizer on an affine normal base. -/
theorem affine_base_prime_exists_global_regular_uniformizer :
    ∃ b : Γ(Y, ⊤), b ≠ 0 ∧ Irreducible (Y.presheaf.germ ⊤ (η : Y) (by trivial) b) := by
  letI := normal_codimensionOne_stalk_DVR η
  letI := Y.presheaf.algebra_section_stalk ⟨(η : Y), show (η : Y) ∈ (⊤ : Y.Opens) from trivial⟩
  letI := (isAffineOpen_top Y).isLocalization_stalk
    ⟨(η : Y), show (η : Y) ∈ (⊤ : Y.Opens) from trivial⟩
  let p := ((isAffineOpen_top Y).primeIdealOf ⟨(η : Y), by trivial⟩).asIdeal
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (η : Y))
  obtain ⟨⟨b, s⟩, heq⟩ := IsLocalization.surj p.primeCompl ϖ
  have hb : Irreducible (algebraMap Γ(Y, ⊤) (Y.presheaf.stalk (η : Y)) b) := by
    rw [← heq]
    exact (irreducible_mul_isUnit (IsLocalization.map_units (Y.presheaf.stalk (η : Y)) s)).mpr hϖ
  refine ⟨b, ?_, ?_⟩
  · intro hz
    apply hb.ne_zero
    rw [hz, map_zero]
  · exact hb

/-- Construct a global effective coefficient-one Cartier base divisor and its irreducible local equation. -/
theorem affine_base_prime_exists_effective_cartier_uniformizer :
    ∃ (H : CartierDivisor Y) (_ : H.IsEffective) (f : Y.functionFieldˣ)
      (_ : H.IsLocalEquationAt (η : Y) f) (a : Y.presheaf.stalk (η : Y)),
      algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField a = (f : Y.functionField) ∧
        Irreducible a ∧ cartierCoefficient H (η : Y) = 1 := by
  obtain ⟨b, hb, hirr⟩ := affine_base_prime_exists_global_regular_uniformizer η
  let f := regularEquationRationalUnit Y ⊤ b hb
  let H := principalCartierDivisor Y f
  let a := Y.presheaf.germ ⊤ (η : Y) (show (η : Y) ∈ (⊤ : Y.Opens) from trivial) b
  have hf : H.IsLocalEquationAt (η : Y) f := CartierDivisor.isLocalEquationAt_principalCartierDivisor _ _
  have ha : algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField a = (f : Y.functionField) := by
    exact Y.algebraMap_germ_eq_germToFunctionField (by trivial) b
  have heff : H.IsEffective := by
    apply CartierDivisor.isEffective_iff_exists.mpr
    intro y
    refine ⟨f, CartierDivisor.isLocalEquationAt_principalCartierDivisor _ _,
      Y.presheaf.germ ⊤ y (by trivial) b, ?_⟩
    exact Y.algebraMap_germ_eq_germToFunctionField (by trivial) b
  have hne : algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField a ≠ 0 := by
    rw [ha]
    exact Units.ne_zero f
  letI := normal_codimensionOne_stalk_DVR η
  have hord : Y.ord (algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField a) (η : Y) = 1 := by
    rw [Y.ord_eq_iff η.property hne]
    simp only [AlgebraicGeometry.Scheme.ordHom]
    rw [Ring.ordFrac_irreducible hirr, WithZero.exp_eq_coe_ofAdd]
  refine ⟨H, heff, f, hf, a, ha, hirr, ?_⟩
  rw [cartierCoefficient_eq_ord hf, ← ha]
  exact hord

end MixedFujita
