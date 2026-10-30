/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperAlgebraicSteinCriterion
public import MixedFujita.BirationalComposition

/-!+Birational model changes preserve the Stein all-open structure-sheaf condition when the
new target is normal and the lifted morphism is proper. The source and target field maps
in the commuting square are actual scheme maps, and relative algebraic closure is transported
through their bijections. No Stein condition for the new morphism is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y T B : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral T] [IsIntegral B]
  (g : X ⟶ Y) (π : T ⟶ X) (ρ : B ⟶ Y) (q : T ⟶ B)
  [IsDominant g] [IsDominant π] [IsDominant ρ] [IsDominant q]

/-- Relative algebraic closure is invariant under commuting birational changes of both
source and target. Only the actual function-field bijections are used. -/
theorem functionField_algebraicallyClosed_of_birational_square
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (hsquare : q ≫ ρ = π ≫ g) (hclosed : FunctionFieldAlgebraicallyClosedInSource g) :
    FunctionFieldAlgebraicallyClosedInSource q := by
  letI : Algebra Y.functionField X.functionField := (dominantFunctionFieldMap g).hom.toAlgebra
  letI : Algebra B.functionField T.functionField := (dominantFunctionFieldMap q).hom.toAlgebra
  have hcomp : (dominantFunctionFieldMap q).hom.comp (dominantFunctionFieldMap ρ).hom =
      (dominantFunctionFieldMap π).hom.comp (dominantFunctionFieldMap g).hom := by
    have heq : dominantFunctionFieldMap (q ≫ ρ) = dominantFunctionFieldMap (π ≫ g) := by
      congr 1
    rw [dominantFunctionFieldMap_comp, dominantFunctionFieldMap_comp] at heq
    exact congrArg CommRingCat.Hom.hom heq
  intro z hz
  obtain ⟨a, rfl⟩ := hπ.2 z
  have ha : IsAlgebraic Y.functionField a :=
    hz.of_ringHom_of_comp_eq (dominantFunctionFieldMap ρ).hom
      (dominantFunctionFieldMap π).hom hρ.2 hπ.1 hcomp
  obtain ⟨b, hb⟩ := hclosed a ha
  refine ⟨(dominantFunctionFieldMap ρ).hom b, ?_⟩
  change ((dominantFunctionFieldMap q).hom.comp (dominantFunctionFieldMap ρ).hom) b = _
  rw [hcomp, RingHom.comp_apply, hb]

/-- The Stein all-open condition survives an actual commuting birational model change.
Normality is needed on the original source and on the new target; the source model itself
need not be assumed normal for this statement. -/
theorem stein_all_open_app_bijective_of_birational_square [IsLocallyNoetherian B] [IsProper q]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (happ : ∀ U : Y.Opens, Function.Surjective (g.app U).hom)
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (hsquare : q ≫ ρ = π ≫ g) :
    ∀ V : B.Opens, Function.Bijective (q.app V).hom := by
  apply proper_all_open_app_bijective_of_functionField_algebraicallyClosed q hnormB
  exact functionField_algebraicallyClosed_of_birational_square g π ρ q hπ hρ hsquare
    (stein_functionField_algebraicallyClosedInSource g happ hnormX)

end MixedFujita
