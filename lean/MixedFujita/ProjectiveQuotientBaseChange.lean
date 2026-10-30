/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveArbitraryBaseChange
public import MixedFujita.ProjTwistingPullback
public import MixedFujita.AffineIdealSheaves
public import Hironaka.Scheme.BlowUp.InverseImage
public import SGA.Foundations.Cohomology.ProjectiveSpaceTwist

/-! Quotient centers and all projective twists commute with coefficient maps. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R S : Type u} [CommRing R] [CommRing S] (I : Ideal R) (φ : R →+* S)

noncomputable local instance projectiveQuotientSourceCommRing : CommRing (R ⧸ I) :=
  Ideal.Quotient.commRing _
noncomputable local instance projectiveQuotientTargetCommRing : CommRing (S ⧸ I.map φ) :=
  Ideal.Quotient.commRing _

theorem quotientCoefficientSpec_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  apply IsPullback.flip
  apply isPullback_of_isClosedImmersion
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Scheme.IdealSheafData.ker_Spec_map_mk (R := CommRingCat.of R) I,
      Scheme.IdealSheafData.ker_Spec_map_mk (R := CommRingCat.of S) (I.map φ)]
    exact specIdealSheaf_comap I φ

theorem projectiveQuotientCoefficient_isPullback (r : ℕ) :
    IsPullback
      (polynomialProjectiveCoefficientMap (n := r)
        (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))
      (polynomialProjectiveToBase r (S ⧸ I.map φ) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))))
      (polynomialProjectiveToBase r (R ⧸ I) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom φ)) :=
  (polynomialProjectiveCoefficientMap_isPullback _).paste_vert
    (quotientCoefficientSpec_isPullback I φ)

variable (r : ℕ) (c : R →+* S)

theorem polynomialProjectiveCoefficient_twistingBundle :
    (projectiveSpace.twistingBundle (Fin r) R).pullback
      (polynomialProjectiveCoefficientMap c) = projectiveSpace.twistingBundle (Fin r) S := by
  unfold projectiveSpace.twistingBundle polynomialProjectiveCoefficientMap
  rw [projTwistingSheaf_pullback]
  congr 1
  funext i
  exact MvPolynomial.map_X c i.down

noncomputable def polynomialProjectiveCoefficientTwistIso (d : ℤ) :
    (Scheme.Modules.pullback (polynomialProjectiveCoefficientMap c)).obj
        (projectiveSpace.twist (Fin r) R d) ≅ projectiveSpace.twist (Fin r) S d :=
  sgaLineBundlePullbackPowerIso _ _ d ≪≫
    eqToIso (congrArg (fun L => L.toModules d) (polynomialProjectiveCoefficient_twistingBundle r c))

end MixedFujita
