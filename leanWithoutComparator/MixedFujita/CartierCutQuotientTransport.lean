/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierCutEuler

/-!
An isomorphism from the actual Cartier ideal subscheme to the next scheme,
commuting with its immersion, constructs the quotient/pushforward comparison
for every Cartier twist. There is no per-degree quotient-isomorphism input.
The unit comparison is proved from the actual structure-sheaf maps of a scheme
isomorphism and functorial pushforward; projection formula gives every twist.
This does not construct a pointed smooth integral cut.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : Scheme.{u}}

theorem schemeUnitToPushforwardUnit_isIso_of_isIso (f : Y ⟶ X) [IsIso f] :
    IsIso (schemeUnitToPushforwardUnit f) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun a : Γ(X, U) ↦ f.app U a)
  exact ConcreteCategory.bijective_of_isIso (f.app U)

noncomputable def idealSubschemePushforwardUnitIsoOfIso
    (I : X.IdealSheafData) (e : I.subscheme ≅ Y) (f : Y ⟶ X)
    (hf : e.inv ≫ I.subschemeι = f) :
    (Scheme.Modules.pushforward I.subschemeι).obj
        (SheafOfModules.unit I.subscheme.ringCatSheaf) ≅
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) := by
  have := schemeUnitToPushforwardUnit_isIso_of_isIso e.inv
  exact (Scheme.Modules.pushforward I.subschemeι).mapIso
      (asIso (schemeUnitToPushforwardUnit e.inv)) ≪≫
    (Scheme.Modules.pushforwardComp e.inv I.subschemeι).app
      (SheafOfModules.unit Y.ringCatSheaf) ≪≫
    (Scheme.Modules.pushforwardCongr hf).app (SheafOfModules.unit Y.ringCatSheaf)

variable [IsIntegral X]

noncomputable def cartierCutQuotientPushforwardIsoOfUnitComparison
    (D E : CartierDivisor X) (hE : E.IsEffective) (f : Y ⟶ X)
    (eUnit : (Scheme.Modules.pushforward (effectiveCartierIdealSheaf E hE).subschemeι).obj
        (SheafOfModules.unit (effectiveCartierIdealSheaf E hE).subscheme.ringCatSheaf) ≅
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) :
    (cartierCutShortComplex D E hE).X₃ ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj D.sheaf) :=
  (cartierIdealSubschemeTwistedPushforwardIso D (effectiveCartierIdealSheaf E hE)).symm ≪≫
    tensorIso (Iso.refl D.sheaf) eUnit ≪≫
      cartierProjectionFormulaIso D f (SheafOfModules.unit Y.ringCatSheaf) ≪≫
        (Scheme.Modules.pushforward f).mapIso
          (rightUnitor ((Scheme.Modules.pullback f).obj D.sheaf))

noncomputable def cartierCutQuotientPushforwardIsoOfSubschemeIso
    (D E : CartierDivisor X) (hE : E.IsEffective)
    (e : (effectiveCartierIdealSheaf E hE).subscheme ≅ Y) (f : Y ⟶ X)
    (hf : e.inv ≫ (effectiveCartierIdealSheaf E hE).subschemeι = f) :
    (cartierCutShortComplex D E hE).X₃ ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj D.sheaf) :=
  cartierCutQuotientPushforwardIsoOfUnitComparison D E hE f
    (idealSubschemePushforwardUnitIsoOfIso (effectiveCartierIdealSheaf E hE) e f hf)

end MixedFujita
