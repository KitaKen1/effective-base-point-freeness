/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedImmersionIdealComparison
public import MixedFujita.ActualBlowupInfinitesimalSheaves
public import MixedFujita.ProjectiveInfinitesimalLayerVanishing
public import Hironaka.Scheme.BlowUp.CoordinateSubspace.ExceptionalProj

/-! The actual exceptional subscheme of a coordinate-center blow-up is
projective space over its actual center ring. The comparison is over the
blow-up and identifies the actual initial infinitesimal quotient globally. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
open CoordinateSubspace
variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n)

noncomputable local instance : CommRing (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) :=
  Ideal.Quotient.commRing _

noncomputable def coordinateExceptionalProjectiveIso :
    (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subscheme ≅
      Proj (MvPolynomial.homogeneousSubmodule (Fin r)
        (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)) :=
  idealSubschemeIsoOfClosedImmersion _ (projInitial A n r hrn) (ker_projInitial A n r hrn)

@[reassoc (attr := simp)]
theorem coordinateExceptionalProjectiveIso_inv_inclusion :
    (coordinateExceptionalProjectiveIso A n r hrn).inv ≫
        (affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι =
      projInitial A n r hrn :=
  idealSubschemeIsoOfClosedImmersion_inv_inclusion _ (projInitial A n r hrn)
    (ker_projInitial A n r hrn)

theorem coordinateExceptionalProjectiveIso_chart (a : centerIdeal A n r) :
    (coordinateExceptionalProjectiveIso A n r hrn).hom ''ᵁ
        ((affineBlowUp.exceptionalIdeal (centerIdeal A n r)).subschemeι ⁻¹ᵁ
          (affineBlowUp.chart (centerIdeal A n r) a).opensRange) =
      (Proj.awayι _ (reesInitialGraded A n r hrn (reesAlgebra.degreeOne (centerIdeal A n r) a))
        (Graded.map_mem (reesInitialGraded A n r hrn) (reesAlgebra.degreeOne_mem a))
        one_pos).opensRange := by
  rw [coordinateExceptionalProjectiveIso,
    idealSubschemeIsoOfClosedImmersion_image_preimage]
  exact projInitial_preimage_opensRange_chart A n r hrn a

variable [IsNoetherianRing A]

noncomputable def coordinateBlowUpInitialProjectiveQuotientIso :
    (unitModule (modelBlowUp A n r)).quotientIdealPow
        (affineBlowUp.π (centerIdeal A n r)) (centerIdeal A n r) 0 ≅
      (Scheme.Modules.pushforward (projInitial A n r hrn)).obj (unitModule _) :=
  affineBlowUpActualExceptionalQuotientIso (centerIdeal A n r) ≪≫
    idealSubschemePushforwardUnitIsoOfKernel _ _ (ker_projInitial A n r hrn)

open TauCeti.AlgebraicGeometry

/-- All positive cohomology of the actual first infinitesimal quotient vanishes.
No integrality, conormal identification, or Jacobson-radical hypothesis is needed. -/
theorem coordinateBlowUp_initial_positive_cohomology_vanish (hs : r + 1 ≤ n) (q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology
      ((unitModule (modelBlowUp A n (r + 1))).quotientIdealPow
        (affineBlowUp.π (centerIdeal A n (r + 1))) (centerIdeal A n (r + 1)) 0) (q + 1)) := by
  let B := MvPolynomial (Fin n) A ⧸ centerIdeal A n (r + 1)
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) B)
  have : Subsingleton ((unitModule P).H (q + 1)) :=
    projectiveSpace.H_structureModule_subsingleton B r q
  have : Subsingleton (Scheme.Modules.Cohomology (unitModule P) (q + 1)) :=
    (sgaCohomologyLinearEquiv (unitModule P) (q + 1)).symm.subsingleton
  have := (closedImmersionCohomologyAddEquiv (projInitial A n (r + 1) hs)
    (unitModule P) (q + 1)).subsingleton
  exact (actualCohomologyLinearEquivOfIso
    (coordinateBlowUpInitialProjectiveQuotientIso A n (r + 1) hs) (q + 1)).subsingleton

end MixedFujita
