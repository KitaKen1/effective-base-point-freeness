/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealSheafModuleFunctor
public import MixedFujita.CartierProjectionFormula
public import MixedFujita.CohomologyOneSectionLifting
public import MixedFujita.CartierTwistExactness

/-! 任意実イデアル閉部分源へのH1からのCartier制限切断全射。 See reports/check-250-BPF-ample-boundary-concentration-extension.json for the verified scope. Original nef-big BPF data internally yield a small effective klt boundary increase with an ample adjoint, retaining L and a0. High-power lc adjoints stay ample for all large degrees. Every coherent ideal subscheme has unconditional full Serre vanishing and actual restriction lifting for high ample twists. The fixed nonempty reduced base source and these concentration-twist extensions are internal. Original L lifting still needs explicit usual KV. Initial and restricted L-nonvanishing, minimal-center normality/vanishing, high-multiplicity concentration, usual KV, BPF and full F1/F2 remain unproved. -/

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






/-- For EVERY actual ideal-sheaf subscheme, actual ideal-twist H1 vanishing
constructs a surjective ORIGINAL Cartier restriction. No image presentation is supplied. -/
theorem idealSheaf_cartier_restriction_exists_surjective_of_H1
    {X : Scheme.{u}} [IsIntegral X] (P : CartierDivisor X) (I : X.IdealSheafData)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1)) :
    ∃ r : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf),
      Function.Surjective (Scheme.Modules.Hom.app r ⊤) := by
  have hseq := cartierTwist_shortExact P (idealSheafDataModuleQuotientSequence_shortExact I)
  have hsurj := Scheme.Modules.sections_surjective hseq hvan
  let r : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf) :=
    (rightUnitor P.sheaf).inv ≫
      (cartierTwistFunctor P).map (schemeUnitToPushforwardUnit I.subschemeι) ≫
      (cartierIdealSubschemeTwistedPushforwardIso P I).hom
  refine ⟨r, ?_⟩
  have hleft := (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (rightUnitor P.sheaf).inv ⊤)).surjective
  have hright := (ConcreteCategory.bijective_of_isIso
    (Scheme.Modules.Hom.app (cartierIdealSubschemeTwistedPushforwardIso P I).hom ⊤)).surjective
  exact hright.comp (hsurj.comp hleft)

end MixedFujita
