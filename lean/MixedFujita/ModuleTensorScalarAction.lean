/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierTwistExactness
public import SGA.Foundations.Cohomology.Statements

/-! Tensor products commute with multiplication by actual global functions.
The proof uses the sheafification universal property and sectionwise tensors. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory Limits Opposite
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}}

@[reassoc]
theorem moduleSmulEnd_naturality {M N : X.Modules} (φ : M ⟶ N) (a : Γ(X, ⊤)) :
    M.smulEnd a ≫ φ = φ ≫ N.smulEnd a := by
  ext U x
  change φ.val.app (op U) (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • x) =
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • φ.val.app (op U) x
  exact (φ.val.app (op U)).hom.map_smul _ _

theorem moduleTensorLeft_smulEnd (L M : X.Modules) (a : Γ(X, ⊤)) :
    (tensorLeft L).map (M.smulEnd a) = (L ⊗ M).smulEnd a := by
  change L ◁ M.smulEnd a = (L ⊗ M).smulEnd a
  apply TauCeti.SheafOfModules.tensor_hom_ext
  erw [← Functor.LaxMonoidal.μ_natural_right]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' (R := Γ(X, U.unop)) (R₂ := Γ(X, U.unop))
    (σ₁₂ := RingHom.id _) (M := Γ(L, U.unop)) (N := Γ(M, U.unop))
    (P₂ := Γ(L ⊗ M, U.unop)) ?_
  intro x y
  let aU : Γ(X, U.unop) := X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a
  let μ : TensorProduct Γ(X, U.unop) Γ(L, U.unop) Γ(M, U.unop) →ₗ[Γ(X, U.unop)]
      Γ(L ⊗ M, U.unop) :=
    (Functor.LaxMonoidal.μ (SheafOfModules.forget X.ringCatSheaf) L M).app U |>.hom
  change μ (x ⊗ₜ[Γ(X, U.unop)] (aU • y)) = aU • μ (x ⊗ₜ[Γ(X, U.unop)] y)
  rw [TensorProduct.tmul_smul, μ.map_smul]

end MixedFujita
