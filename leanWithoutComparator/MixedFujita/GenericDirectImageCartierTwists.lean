/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ExceptionalGenericDirectImage
public import MixedFujita.ModuleOpenFrameCoefficients
public import MixedFujita.ModulePushforwardTensorComparisons
public import MixedFujita.CartierProjectionFormula

/-! Transfer the actual generic-open exceptional direct-image frame to the
actual open scheme. The existing projection formula and open tensor comparison
then construct the corresponding isomorphism for every actual Cartier twist,
including the same model's actual moduli Cartier multiple. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {T B Y : Scheme.{u}} [IsIntegral T] [IsIntegral B] [IsIntegral Y]
  (q : T ⟶ B) (ρ : B ⟶ Y) (E : CartierDivisor T) (hE : E.IsEffective)
  (W : Y.Opens) [IsIso (ρ ∣_ W)]
  [IsIso (effectiveCartierPushforwardUnitMap (q ≫ ρ) E hE)]

/-- The actual unit frame of the same exceptional direct image on the open scheme. -/
noncomputable def exceptionalModifiedBaseRestrictUnitIso :
    ((Scheme.Modules.pushforward q).obj E.sheaf).restrict (ρ ⁻¹ᵁ W).ι ≅
      SheafOfModules.unit ((ρ ⁻¹ᵁ W) : Scheme).ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv (ρ ⁻¹ᵁ W)).app
    ((Scheme.Modules.pushforward q).obj E.sheaf)).symm ≪≫
    (Scheme.Modules.overEquiv (ρ ⁻¹ᵁ W)).functor.mapIso
      (exceptionalModifiedBaseUnitOverIso q ρ E hE W).symm ≪≫
    (ρ ⁻¹ᵁ W).sheafOfModulesEquivOverUnit B.ringCatSheaf

/-- All actual Cartier twists use the same model, divisor, generic open and projection formula. -/
noncomputable def exceptionalModifiedBaseCartierTwistIso (A : CartierDivisor B) :
    A.sheaf.restrict (ρ ⁻¹ᵁ W).ι ≅
      ((Scheme.Modules.pushforward q).obj
        ((Scheme.Modules.pullback q).obj A.sheaf ⊗ E.sheaf)).restrict (ρ ⁻¹ᵁ W).ι :=
  (rightUnitor (A.sheaf.restrict (ρ ⁻¹ᵁ W).ι)).symm ≪≫
    tensorIso (Iso.refl _) (exceptionalModifiedBaseRestrictUnitIso q ρ E hE W).symm ≪≫
    moduleOpenRestrictionTensorIso (ρ ⁻¹ᵁ W).ι A.sheaf
      ((Scheme.Modules.pushforward q).obj E.sheaf) ≪≫
    (Scheme.Modules.restrictFunctor (ρ ⁻¹ᵁ W).ι).mapIso
      (cartierProjectionFormulaIso A q E.sheaf)

end MixedFujita
