/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoordinateExceptionalBaseChange
public import MixedFujita.ProjectiveQuotientBaseChange

/-! The exceptional scheme of a flat coordinate base change is the standard
projective space over the quotient of the target ring. The identification is
over the actual blow-up, and transports every restricted Rees twist. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits CoordinateSubspace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n)
  {S : Type u} [CommRing S] (φ : MvPolynomial (Fin n) A →+* S)
noncomputable local instance coordinateStandardSourceCommRing :
    CommRing (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) := Ideal.Quotient.commRing _
noncomputable local instance coordinateStandardTargetCommRing :
    CommRing (S ⧸ (centerIdeal A n r).map φ) := Ideal.Quotient.commRing _

theorem coordinateProjInitial_toPolynomialBase :
    projInitial A n r hrn ≫ affineBlowUp.π (centerIdeal A n r) =
      polynomialProjectiveToBase r (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal A n r))) := by
  rw [projInitial_π, polynomialProjectiveToBase, Category.assoc]
  congr 2


variable (hφ : φ.Flat)

include hφ in
theorem coordinateExceptionalBaseChanged_overBase_isPullback :
    IsPullback (coordinateExceptionalBaseChangedProjection A n r hrn φ)
      (coordinateExceptionalBaseChangedInclusion A n r hrn φ ≫
        affineBlowUp.π ((centerIdeal A n r).map φ))
      (polynomialProjectiveToBase r (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (centerIdeal A n r))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  rw [← coordinateProjInitial_toPolynomialBase A n r hrn]
  exact (IsPullback.of_hasPullback (affineBlowUp.mapOfEq φ rfl)
    (projInitial A n r hrn)).flip.paste_vert (affineBlowUp_mapOfEq_isPullback_of_flat φ rfl hφ)

noncomputable def coordinateExceptionalStandardBaseChangeIso :
    coordinateExceptionalBaseChangedScheme A n r hrn φ ≅
      polynomialProjectiveScheme r (S ⧸ (centerIdeal A n r).map φ) :=
  (coordinateExceptionalBaseChanged_overBase_isPullback A n r hrn φ hφ).isoIsPullback _ _
    (projectiveQuotientCoefficient_isPullback (centerIdeal A n r) φ r)

theorem coordinateExceptionalStandardBaseChangeIso_inv_projection :
    (coordinateExceptionalStandardBaseChangeIso A n r hrn φ hφ).inv ≫
        coordinateExceptionalBaseChangedProjection A n r hrn φ =
      polynomialProjectiveCoefficientMap
        (Ideal.quotientMap ((centerIdeal A n r).map φ) φ Ideal.le_comap_map) :=
  (coordinateExceptionalBaseChanged_overBase_isPullback A n r hrn φ hφ).isoIsPullback_inv_fst _ _
    (projectiveQuotientCoefficient_isPullback (centerIdeal A n r) φ r)

noncomputable def coordinateBaseChangedProjectiveImmersion :
    polynomialProjectiveScheme r (S ⧸ (centerIdeal A n r).map φ) ⟶
      affineBlowUp ((centerIdeal A n r).map φ) :=
  (coordinateExceptionalStandardBaseChangeIso A n r hrn φ hφ).inv ≫
    coordinateExceptionalBaseChangedInclusion A n r hrn φ

instance coordinateBaseChangedProjectiveImmersion_isClosedImmersion :
    IsClosedImmersion (coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ) :=
  inferInstanceAs (IsClosedImmersion (_ ≫ coordinateExceptionalBaseChangedInclusion A n r hrn φ))

theorem coordinateBaseChangedProjectiveImmersion_ker :
    (coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ).ker =
      affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ) := by
  rw [coordinateBaseChangedProjectiveImmersion, Scheme.Hom.ker_comp_of_isIso,
    coordinateExceptionalBaseChangedInclusion_ker]

noncomputable def coordinateBaseChangedExceptionalProjectiveIso :
    (affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ)).subscheme ≅
      polynomialProjectiveScheme r (S ⧸ (centerIdeal A n r).map φ) :=
  idealSubschemeIsoOfClosedImmersion _ _ (coordinateBaseChangedProjectiveImmersion_ker A n r hrn φ hφ)

theorem coordinateBaseChangedExceptionalProjectiveIso_inv_inclusion :
    (coordinateBaseChangedExceptionalProjectiveIso A n r hrn φ hφ).inv ≫
        (affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ)).subschemeι =
      coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ :=
  idealSubschemeIsoOfClosedImmersion_inv_inclusion _ _
    (coordinateBaseChangedProjectiveImmersion_ker A n r hrn φ hφ)

noncomputable def coordinateBaseChangedStandardReesRestrictionIso (d : ℤ) :
    (Scheme.Modules.pullback (coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ)).obj
        ((coordinateBaseChangedReesBundle A n r hrn φ).toModules d) ≅
      projectiveSpace.twist (Fin r) (S ⧸ (centerIdeal A n r).map φ) d := by
  let e := coordinateExceptionalStandardBaseChangeIso A n r hrn φ hφ
  let p := coordinateExceptionalBaseChangedInclusion A n r hrn φ
  let q := coordinateExceptionalBaseChangedProjection A n r hrn φ
  let M := projectiveSpace.twist (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) d
  exact ((Scheme.Modules.pullbackComp e.inv p).app _).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso (coordinateBaseChangedReesRestrictionIso A n r hrn φ d) ≪≫
    (Scheme.Modules.pullbackComp e.inv q).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (coordinateExceptionalStandardBaseChangeIso_inv_projection A n r hrn φ hφ)).app M ≪≫
    polynomialProjectiveCoefficientTwistIso r _ d

end MixedFujita
