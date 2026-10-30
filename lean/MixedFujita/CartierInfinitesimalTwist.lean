/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalQuotientFunctor
public import MixedFujita.InfinitesimalThickeningSubscheme
public import MixedFujita.CartierProjectionFormula

/-! Cartier twisting of the actual infinitesimal tower and its actual kernels.
For every thickness, the quotient of a Cartier sheaf is identified with
the pushforward of its restriction to the actual closed thickening. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
open TauCeti.AlgebraicGeometry.Scheme
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec A) (I : Ideal A) (D : CartierDivisor X)

noncomputable def cartierTensorInfinitesimalQuotientIso (M : X.Modules) (n : ℕ) :
    D.sheaf ⊗ M.quotientIdealPow f I n ≅ (D.sheaf ⊗ M).quotientIdealPow f I n :=
  infinitesimalQuotientFunctorIso f I (cartierTwistFunctor D)
    (moduleTensorLeft_smulEnd D.sheaf) M n

@[reassoc (attr := simp)]
theorem cartierTensorInfinitesimalQuotientIso_quotient (M : X.Modules) (n : ℕ) :
    (cartierTwistFunctor D).map (M.toQuotientIdealPow f I n) ≫
        (cartierTensorInfinitesimalQuotientIso f I D M n).hom =
      (D.sheaf ⊗ M).toQuotientIdealPow f I n :=
  infinitesimalQuotientFunctorIso_quotient f I (cartierTwistFunctor D)
    (moduleTensorLeft_smulEnd D.sheaf) M n

@[reassoc]
theorem cartierTensorInfinitesimalQuotientIso_transition (M : X.Modules) (n : ℕ) :
    (cartierTwistFunctor D).map (M.quotientIdealPowMap f I n) ≫
        (cartierTensorInfinitesimalQuotientIso f I D M n).hom =
      (cartierTensorInfinitesimalQuotientIso f I D M (n + 1)).hom ≫
        (D.sheaf ⊗ M).quotientIdealPowMap f I n :=
  infinitesimalQuotientFunctorIso_transition f I (cartierTwistFunctor D)
    (moduleTensorLeft_smulEnd D.sheaf) M n

noncomputable def cartierInfinitesimalQuotientIso (n : ℕ) :
    D.sheaf ⊗ (unitModule X).quotientIdealPow f I n ≅ D.sheaf.quotientIdealPow f I n :=
  cartierTensorInfinitesimalQuotientIso f I D (unitModule X) n ≪≫
    (infinitesimalQuotientFunctor f I n).mapIso (rightUnitor D.sheaf)

@[reassoc (attr := simp)]
theorem cartierInfinitesimalQuotientIso_quotient (n : ℕ) :
    (cartierTwistFunctor D).map ((unitModule X).toQuotientIdealPow f I n) ≫
        (cartierInfinitesimalQuotientIso f I D n).hom =
      (rightUnitor D.sheaf).hom ≫ D.sheaf.toQuotientIdealPow f I n := by
  simp only [cartierInfinitesimalQuotientIso, Iso.trans_hom,
    cartierTensorInfinitesimalQuotientIso_quotient_assoc, Functor.mapIso_hom,
    infinitesimalQuotientFunctor]
  exact infinitesimalQuotientMap_quotient f I (rightUnitor D.sheaf).hom n

@[reassoc]
theorem cartierInfinitesimalQuotientIso_transition (n : ℕ) :
    (cartierTwistFunctor D).map ((unitModule X).quotientIdealPowMap f I n) ≫
        (cartierInfinitesimalQuotientIso f I D n).hom =
      (cartierInfinitesimalQuotientIso f I D (n + 1)).hom ≫
        D.sheaf.quotientIdealPowMap f I n := by
  simp only [cartierInfinitesimalQuotientIso, Iso.trans_hom, Category.assoc,
    cartierTensorInfinitesimalQuotientIso_transition_assoc, Functor.mapIso_hom,
    infinitesimalQuotientFunctor, ← infinitesimalQuotientMap_transition]

noncomputable def cartierInfinitesimalLayerIso (n : ℕ) :
    D.sheaf ⊗ infinitesimalCohomologyLayer f I (unitModule X) n ≅
      infinitesimalCohomologyLayer f I D.sheaf n :=
  asIso (kernelComparison ((unitModule X).quotientIdealPowMap f I n)
    (cartierTwistFunctor D)) ≪≫
      kernel.mapIso _ _ (cartierInfinitesimalQuotientIso f I D (n + 1))
        (cartierInfinitesimalQuotientIso f I D n)
        (cartierInfinitesimalQuotientIso_transition f I D n)

@[reassoc]
theorem cartierInfinitesimalLayerIso_inclusion (n : ℕ) :
    (cartierInfinitesimalLayerIso f I D n).hom ≫
        kernel.ι (D.sheaf.quotientIdealPowMap f I n) =
      (cartierTwistFunctor D).map
        (kernel.ι ((unitModule X).quotientIdealPowMap f I n)) ≫
          (cartierInfinitesimalQuotientIso f I D (n + 1)).hom := by
  simp [cartierInfinitesimalLayerIso, kernel.map, kernelComparison_comp_ι_assoc]

variable [IsNoetherianRing A]

/-- The thickening may be nonreduced; its actual restriction is used. -/
noncomputable def cartierInfinitesimalThickeningIso (n : ℕ) :
    D.sheaf.quotientIdealPow f I n ≅
      (Scheme.Modules.pushforward ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subschemeι).obj
        ((Scheme.Modules.pullback ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subschemeι).obj
          D.sheaf) :=
  (cartierInfinitesimalQuotientIso f I D n).symm ≪≫
    (cartierTwistFunctor D).mapIso (infinitesimalQuotientIdealSubschemeIso f I n) ≪≫
      cartierIdealSubschemeTwistedPushforwardIso D _

end MixedFujita
