/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinAlgebraicFunctionField
public import MixedFujita.ProperBirationalSections
public import SGA.Foundations.Cohomology.SteinFactorization

/-!+The function-field criterion for the all-open Stein condition. Properness makes regular
functions over affine target opens algebraic over the target function field. Relative
algebraic closure descends them rationally; valuation domination and normal Hartogs descend
them regularly. The sheaf basis criterion then supplies all opens, including the empty open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (g : X ⟶ Y) [IsDominant g]

/-- Relative algebraic closure for the actual dominant map of scheme function fields. -/
def FunctionFieldAlgebraicallyClosedInSource : Prop :=
  ∀ z : X.functionField, (letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap g).hom.toAlgebra; IsAlgebraic Y.functionField z) →
    ∃ a : Y.functionField, (dominantFunctionFieldMap g).hom a = z

/-- The all-open Stein property of a normal source implies relative algebraic closure. -/
theorem stein_functionField_algebraicallyClosedInSource
    (happ : ∀ U : Y.Opens, Function.Surjective (g.app U).hom)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    FunctionFieldAlgebraicallyClosedInSource g := by
  intro z hz
  obtain ⟨_, ⟨U, hU, rfl⟩, hη, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  haveI : Nonempty U := ⟨⟨genericPoint Y, hη⟩⟩
  exact stein_rationalFunction_in_image_of_isAlgebraic g happ hnorm U hU z hz

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- A regular function over an affine target open is algebraic over the target function
field for a proper morphism to a locally Noetherian scheme. -/
theorem proper_affine_section_rational_isAlgebraic [IsLocallyNoetherian Y] [IsProper g]
    (U : Y.Opens) [Nonempty U] [Nonempty (g ⁻¹ᵁ U)]
    (hU : IsAffineOpen U) (s : Γ(X, g ⁻¹ᵁ U)) :
    letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap g).hom.toAlgebra
    IsAlgebraic Y.functionField (X.germToFunctionField (g ⁻¹ᵁ U) s) := by
  haveI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap g).hom.toAlgebra
  letI : Algebra Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
  letI : Algebra Γ(Y, U) X.functionField :=
    ((dominantFunctionFieldMap g).hom.comp (Y.germToFunctionField U).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower Γ(Y, U) Γ(X, g ⁻¹ᵁ U) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change (dominantFunctionFieldMap g).hom (Y.germToFunctionField U a) =
      X.germToFunctionField (g ⁻¹ᵁ U) ((g.app U).hom a)
    simpa only [Scheme.Hom.appLE_eq_app] using
      dominantFunctionFieldMap_germ g U (g ⁻¹ᵁ U) le_rfl a
  haveI : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) :=
    CohomologyAux.finite_app_of_isProper g hU
  have hs : IsIntegral Γ(Y, U) (X.germToFunctionField (g ⁻¹ᵁ U) s) :=
    (Algebra.IsIntegral.isIntegral s).map
      (IsScalarTower.toAlgHom Γ(Y, U) Γ(X, g ⁻¹ᵁ U) X.functionField)
  exact (hs.tower_top (A := Y.functionField)).isAlgebraic

/-- A target rational function regular after proper dominant pullback is regular on the
entire target open, by valuation domination in codimension one and normal Hartogs. -/
theorem proper_exists_regular_function_of_pullback_regular [IsLocallyNoetherian Y]
    [IsProper g] (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (U : Y.Opens) [Nonempty U] (a : Y.functionField)
    (hreg : ∀ t ∈ g ⁻¹ᵁ U, (dominantFunctionFieldMap g).hom a ∈
      (algebraMap (X.presheaf.stalk t) X.functionField).range) :
    ∃ s : Γ(Y, U), Y.germToFunctionField U s = a := by
  apply exists_section_of_forall_mem_stalk_range U a
  intro y hy
  apply mem_range_stalk_of_codimOne hnorm y U hy
  intro ξ hξU hξ
  obtain ⟨t, rfl⟩ := surjective_of_isProper_of_isDominant g ξ
  haveI := hnorm (g t)
  haveI := valuationRing_stalk_of_coheight_eq_one (g t) hξ
  exact mem_range_stalk_of_pullback g t a (hreg t hξU)

/-- Properness, normality of the target and relative algebraic closure imply bijections
on structure-sheaf sections for every target open. No Stein certificate is assumed. -/
theorem proper_all_open_app_bijective_of_functionField_algebraicallyClosed
    [IsLocallyNoetherian Y] [IsProper g]
    (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hclosed : FunctionFieldAlgebraicallyClosedInSource g) :
    ∀ V : Y.Opens, Function.Bijective (g.app V).hom := by
  intro V
  have hiso : IsIso (g.app V) := by
    apply CohomologyAux.isIso_app_of_basis g _ V
    intro W y hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUW⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy W.isOpen
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    haveI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
    refine ⟨U, hyU, hUW, (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩⟩
    · intro a b hab
      apply Y.germToFunctionField_injective U
      apply (dominantFunctionFieldMap g).hom.injective
      simp only [dominantFunctionFieldMap_germ g U (g ⁻¹ᵁ U) le_rfl,
        Scheme.Hom.appLE_eq_app, hab]
    · intro s
      obtain ⟨a, ha⟩ := hclosed (X.germToFunctionField (g ⁻¹ᵁ U) s)
        (proper_affine_section_rational_isAlgebraic g U hU s)
      obtain ⟨b, hb⟩ := proper_exists_regular_function_of_pullback_regular g hnorm U a
        (fun t ht => ⟨X.presheaf.germ (g ⁻¹ᵁ U) t ht s, by
          rw [X.algebraMap_germ_eq_germToFunctionField ht, ha]⟩)
      refine ⟨b, X.germToFunctionField_injective (g ⁻¹ᵁ U) ?_⟩
      rw [← Scheme.Hom.appLE_eq_app, ← dominantFunctionFieldMap_germ, hb, ha]
  exact ConcreteCategory.bijective_of_isIso (g.app V)

end MixedFujita
