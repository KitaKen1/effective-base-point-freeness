/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.QuasicoherentImageIdealSheaf
public import MixedFujita.CartierProjectionFormula
public import MixedFujita.CohomologyOneSectionLifting

/-! 実像イデアル閉部分源へのCartier制限とH1による切断全射。 See reports/check-245-lc-kernel-closed-subscheme-lifting.json for the verified scope. The canonical lc kernel gives a proper nonzero actual image ideal, a concrete nonzero untwisted quotient unit, and a nonempty lower-dimensional actual closed subscheme W. Usual KV gives actual Cartier restriction section lifting to W. Usual KV itself and nonzero/generating sections of P restricted to W remain unproved; W is not identified with a reduced lc center; klt BPF and full F1/F2 remain incomplete. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The ACTUAL Cartier restriction map to the actual image-ideal subscheme.
Projection formula constructs the target comparison for every Cartier class. -/
noncomputable def quasicoherentImageIdealCartierRestriction
    {X : Scheme.{u}} [IsIntegral X] (P : CartierDivisor X)
    (M : X.Modules) [M.IsQuasicoherent] (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    P.sheaf ⟶ (Scheme.Modules.pushforward (quasicoherentModuleImageIdealSheaf M j).subschemeι).obj
      ((Scheme.Modules.pullback (quasicoherentModuleImageIdealSheaf M j).subschemeι).obj P.sheaf) :=
  (rightUnitor P.sheaf).inv ≫
    (cartierTwistFunctor P).map
      (schemeUnitToPushforwardUnit (quasicoherentModuleImageIdealSheaf M j).subschemeι) ≫
    (cartierIdealSubschemeTwistedPushforwardIso P (quasicoherentModuleImageIdealSheaf M j)).hom


/-- Vanishing of the ORIGINAL kernel twist lifts sections to the actual pulled Cartier
line on the actual image-ideal subscheme, with all quotient comparisons internal. -/
theorem quasicoherentImageIdealCartierRestriction_surjective_of_H1
    {X : Scheme.{u}} [IsIntegral X] (P : CartierDivisor X)
    (M : X.Modules) [M.IsQuasicoherent] (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (hvan : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ M) 1)) :
    Function.Surjective (Scheme.Modules.Hom.app
      (quasicoherentImageIdealCartierRestriction P M j) ⊤) := by
  let I := quasicoherentModuleImageIdealSheaf M j
  have hseq := cartierTwist_shortExact P (quasicoherentImageIdealShortComplex_shortExact j)
  have hsurj := Scheme.Modules.sections_surjective hseq hvan
  have hleft := (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (rightUnitor P.sheaf).inv ⊤)).surjective
  have hright := (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (cartierIdealSubschemeTwistedPushforwardIso P I).hom ⊤)).surjective
  exact hright.comp (hsurj.comp hleft)

end MixedFujita
