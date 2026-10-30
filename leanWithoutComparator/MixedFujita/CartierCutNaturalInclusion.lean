/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
import all TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
import all TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Monoidal
import all TauCeti.AlgebraicGeometry.CartierDivisor.TensorProduct
public import MixedFujita.CartierCutEuler
public import MixedFujita.CartierIdealPowerLayers

/-! The tensor-defined Cartier cut map is the natural inclusion of rational
sections. Thus the natural Cartier cokernel is the actual closed restriction. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} [IsIntegral X]

theorem cartierTensorSheafIso_presheaf (D E : CartierDivisor X) :
    Functor.LaxMonoidal.μ (SheafOfModules.forget X.ringCatSheaf) D.sheaf E.sheaf ≫
        (SheafOfModules.forget X.ringCatSheaf).map (cartierTensorSheafIso D E).hom =
      CartierDivisor.tensorPresheafHom D E := by
  have h : (D.sheaf.tensorUnderlyingIso E.sheaf).inv ≫ (cartierTensorSheafIso D E).hom =
      (TauCeti.SheafOfModules.tensorProductIso X.sheaf D.sheaf E.sheaf).inv ≫
        (CartierDivisor.tensorProductSheafIso D E).hom := by
    simp only [cartierTensorSheafIso, Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id_assoc]
  erw [TauCeti.SheafOfModules.forget_μ X.sheaf, Category.assoc, ← Functor.map_comp, h]
  simp only [CartierDivisor.tensorProductSheafIso, Iso.trans_hom, asIso_hom,
    Iso.inv_hom_id_assoc]
  apply ((TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf).unit_comp_map_eq_iff
    _ _).2
  erw [TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app X.sheaf]

omit [IsIntegral X] in
theorem moduleForget_tensor_rightUnitor (M : X.Modules) :
    Functor.LaxMonoidal.μ (SheafOfModules.forget X.ringCatSheaf) M
        (SheafOfModules.unit X.ringCatSheaf) ≫
        (SheafOfModules.forget X.ringCatSheaf).map (rightUnitor M).hom =
      (rightUnitor M.val).hom := by
  have h := Functor.LaxMonoidal.right_unitality (SheafOfModules.forget X.ringCatSheaf) M
  erw [TauCeti.SheafOfModules.forget_ε X.sheaf, whiskerLeft_id, Category.id_comp] at h
  exact h.symm

theorem cartierTensor_negativeToUnit_toRationalFunctions (D E : CartierDivisor X)
    (hE : E.IsEffective) :
    (cartierTensorSheafIso D (-E)).hom ≫ (D + -E).sheafι =
      (cartierTwistFunctor D).map (negativeCartierToUnit X E hE) ≫
        (rightUnitor D.sheaf).hom ≫ D.sheafι := by
  apply TauCeti.SheafOfModules.tensor_hom_ext
  simp only [Functor.map_comp, ← Category.assoc, cartierTensorSheafIso_presheaf]
  erw [← Functor.LaxMonoidal.μ_natural_right]
  simp only [Category.assoc]
  erw [← Category.assoc _ _ ((SheafOfModules.forget X.ringCatSheaf).map D.sheafι),
    moduleForget_tensor_rightUnitor (X := X) D.sheaf]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' (R := Γ(X, U.unop)) (R₂ := Γ(X, U.unop))
    (σ₁₂ := RingHom.id _) (M := Γ(D.sheaf, U.unop)) (N := Γ((-E).sheaf, U.unop))
    (P₂ := Γ(rationalFunctions X, U.unop)) ?_
  intro s t
  let a : Γ(X, U.unop) := (negativeCartierToUnit X E hE).val.app U t
  change Scheme.Modules.Hom.app (D + -E).sheafι U.unop
      (CartierDivisor.sectionsMul D (-E) U.unop s t) =
    Scheme.Modules.Hom.app D.sheafι U.unop
      (a • s)
  rw [CartierDivisor.sheafι_app_sectionsMul, Scheme.Modules.Hom.app_smul]
  have ht := congrArg (fun φ => Scheme.Modules.Hom.app φ U.unop t)
    (negativeCartierToUnit_toRationalFunctions X E hE)
  change Scheme.Modules.Hom.app (toRationalFunctions X) U.unop
      (Scheme.Modules.Hom.app (negativeCartierToUnit X E hE) U.unop t) =
    Scheme.Modules.Hom.app (-E).sheafι U.unop t at ht
  rw [← ht]
  apply (rationalFunctionsSectionsEquiv X U.unop).injective
  rw [rationalFunctionsSectionsEquiv_mulBilin, rationalFunctionsSectionsEquiv_smul,
    toRationalFunctionsRing_app, mul_comm]
  rfl

theorem cartierCutShortComplex_first_map_eq_inclusion (D E : CartierDivisor X)
    (hE : E.IsEffective) :
    (cartierCutShortComplex D E hE).f = cartierEffectiveInclusion D E hE := by
  apply (cancel_mono D.sheafι).mp
  rw [cartierEffectiveInclusion_ι, cartierCutShortComplex_first_map,
    Category.assoc, Category.assoc, ← cartierTensor_negativeToUnit_toRationalFunctions]
  simp only [cartierCutTensorSourceIso, Iso.trans_inv, eqToIso, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact cartierSheafEqToHom_inclusion (sub_eq_add_neg D E)

end MixedFujita
