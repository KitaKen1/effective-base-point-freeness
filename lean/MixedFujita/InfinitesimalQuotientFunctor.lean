/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleTensorScalarAction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! The actual quotient tower is functorial in its coefficient sheaf.
Colimit-preserving functors that respect global scalar multiplication
commute with this tower, including its transition morphisms. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A : CommRingCat.{u}} {X : Scheme.{u}}
  (f : X ⟶ Spec A) (I : Ideal A)

noncomputable def infinitesimalQuotientMap {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    M.quotientIdealPow f I n ⟶ N.quotientIdealPow f I n :=
  cokernel.desc _ (φ ≫ N.toQuotientIdealPow f I n) (by
    apply Sigma.hom_ext
    intro a
    simp only [Scheme.Modules.idealPowSMul, Sigma.ι_comp_desc_assoc, comp_zero,
      moduleSmulEnd_naturality_assoc, N.smulEnd_toQuotientIdealPow f I a.1 a.2])

@[reassoc (attr := simp)]
theorem infinitesimalQuotientMap_quotient {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    M.toQuotientIdealPow f I n ≫ infinitesimalQuotientMap f I φ n =
      φ ≫ N.toQuotientIdealPow f I n :=
  cokernel.π_desc _ _ _

noncomputable def infinitesimalQuotientFunctor (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := M.quotientIdealPow f I n
  map φ := infinitesimalQuotientMap f I φ n
  map_id M := by
    apply (cancel_epi (M.toQuotientIdealPow f I n)).mp
    simp
  map_comp {M N P} φ ψ := by
    apply (cancel_epi (M.toQuotientIdealPow f I n)).mp
    simp

@[reassoc]
theorem infinitesimalQuotientMap_transition {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    infinitesimalQuotientMap f I φ (n + 1) ≫ N.quotientIdealPowMap f I n =
      M.quotientIdealPowMap f I n ≫ infinitesimalQuotientMap f I φ n := by
  apply (cancel_epi (M.toQuotientIdealPow f I (n + 1))).mp
  simp

variable (F : X.Modules ⥤ X.Modules) [F.PreservesZeroMorphisms]
  [PreservesColimitsOfSize.{u,u} F]
  (hF : ∀ (M : X.Modules) (a : Γ(X, ⊤)), F.map (M.smulEnd a) = (F.obj M).smulEnd a)

include hF in
omit [F.PreservesZeroMorphisms] in
theorem infinitesimalIdealPowSMul_functor (M : X.Modules) (n : ℕ) :
    F.map (M.idealPowSMul f I n) =
      (PreservesCoproduct.iso F (fun _ : (I ^ (n + 1) : Ideal A) ↦ M)).hom ≫
        (F.obj M).idealPowSMul f I n := by
  let e := PreservesCoproduct.iso F (fun _ : (I ^ (n + 1) : Ideal A) ↦ M)
  have h : e.inv ≫ F.map (M.idealPowSMul f I n) = (F.obj M).idealPowSMul f I n := by
    change sigmaComparison F (fun _ : (I ^ (n + 1) : Ideal A) ↦ M) ≫
      F.map (M.idealPowSMul f I n) = _
    apply Sigma.hom_ext
    intro a
    simp only [ι_comp_sigmaComparison_assoc, ← F.map_comp, Scheme.Modules.idealPowSMul,
      Sigma.ι_comp_desc, hF]
  calc
    F.map (M.idealPowSMul f I n) = e.hom ≫ (e.inv ≫ F.map (M.idealPowSMul f I n)) := by
      rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    _ = e.hom ≫ (F.obj M).idealPowSMul f I n := by rw [h]

noncomputable def infinitesimalQuotientFunctorIso (M : X.Modules) (n : ℕ) :
    F.obj (M.quotientIdealPow f I n) ≅ (F.obj M).quotientIdealPow f I n :=
  PreservesCokernel.iso F (M.idealPowSMul f I n) ≪≫
    cokernel.mapIso _ _
      (PreservesCoproduct.iso F (fun _ : (I ^ (n + 1) : Ideal A) ↦ M)) (Iso.refl _)
      (by simpa using infinitesimalIdealPowSMul_functor f I F hF M n)

@[reassoc (attr := simp)]
theorem infinitesimalQuotientFunctorIso_quotient (M : X.Modules) (n : ℕ) :
    F.map (M.toQuotientIdealPow f I n) ≫
        (infinitesimalQuotientFunctorIso f I F hF M n).hom =
      (F.obj M).toQuotientIdealPow f I n := by
  simp [infinitesimalQuotientFunctorIso, cokernel.map]

@[reassoc]
theorem infinitesimalQuotientFunctorIso_transition (M : X.Modules) (n : ℕ) :
    F.map (M.quotientIdealPowMap f I n) ≫
        (infinitesimalQuotientFunctorIso f I F hF M n).hom =
      (infinitesimalQuotientFunctorIso f I F hF M (n + 1)).hom ≫
        (F.obj M).quotientIdealPowMap f I n := by
  apply (cancel_epi (F.map (M.toQuotientIdealPow f I (n + 1)))).mp
  rw [← F.map_comp_assoc, Scheme.Modules.toQuotientIdealPow_comp_map]
  simp

end MixedFujita
