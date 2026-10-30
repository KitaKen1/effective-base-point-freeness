/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionsEmbedding
public import MixedFujita.ProjTwistingPullback
public import MixedFujita.AffineBlowupIntegralCartier

/-! Explicit regular sections on Rees charts and their transition equations. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite HomogeneousLocalization
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (I : Ideal R)

noncomputable def reesConstantSection (r : R) (U : (affineBlowUp I).Opens) :
    Γ(affineBlowUp I, U) :=
  Proj.fracSection (reesAlgebra.grading I) (reesAlgebra.algebraMap_mem_grading_zero r)
    (SetLike.GradedOne.one_mem) U (by simp)

theorem reesConstantSection_restrict (r : R) {U V : (affineBlowUp I).Opens} (h : V ≤ U) :
    (affineBlowUp I).presheaf.map (homOfLE h).op (reesConstantSection I r U) =
      reesConstantSection I r V := rfl

theorem reesConstantSection_eq_awayToSection (r : R) (a : I) :
    reesConstantSection I r (Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) =
      Proj.awayToSection (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
        (fromZeroRingHom (reesAlgebra.grading I) _ ((reesAlgebra.gradingZeroEquiv I).symm r)) := by
  apply Proj.section_ext
  intro x
  change Localization.mk _ _ = _
  simp only [Proj.awayToSection, ProjectiveSpectrum.Proj.awayToSection,
    CommRingCat.hom_ofHom]
  rfl

theorem affineBlowUp_chart_appLE_awayToSection (a : I)
    (z : Away (reesAlgebra.grading I) (reesAlgebra.degreeOne I a))
    (e : (⊤ : (Spec (.of (affineBlowUpAlgebra I a))).Opens) ≤
      affineBlowUp.chart I a ⁻¹ᵁ Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) :
    (affineBlowUp.chart I a).appLE _ ⊤ e
        (Proj.awayToSection (reesAlgebra.grading I) (reesAlgebra.degreeOne I a) z) =
      (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv (reesAlgebra.chartRingEquiv a z) := by
  let B := CommRingCat.of (affineBlowUpAlgebra I a)
  let ev := (Scheme.ΓSpecIso B).inv.hom.comp (reesAlgebra.chartIso I a).hom.hom
  have he : (Spec B).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ev) ≫
      Proj.awayι (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
        (reesAlgebra.degreeOne_mem a) one_pos = affineBlowUp.chart I a := by
    change (Spec B).toSpecΓ ≫ Spec.map
      ((reesAlgebra.chartIso I a).hom ≫ (Scheme.ΓSpecIso B).inv) ≫ _ = _
    simp only [Spec.map_comp, ← Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.id_comp]
    rfl
  have h := proj_awayι_appLE_awayToSection (reesAlgebra.grading I)
    (reesAlgebra.degreeOne I a) (reesAlgebra.degreeOne_mem a) one_pos ev z
    (by rw [he]; exact e)
  have hv : ev z = (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv
      (reesAlgebra.chartRingEquiv a z) := rfl
  simpa only [he, hv] using h

theorem affineBlowUp_chart_appLE_constant (a : I) (r : R)
    (e : (⊤ : (Spec (.of (affineBlowUpAlgebra I a))).Opens) ≤
      affineBlowUp.chart I a ⁻¹ᵁ Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) :
    (affineBlowUp.chart I a).appLE _ ⊤ e (reesConstantSection I r _) =
      (Scheme.ΓSpecIso (.of (affineBlowUpAlgebra I a))).inv
        (algebraMap R (affineBlowUpAlgebra I a) r) := by
  rw [reesConstantSection_eq_awayToSection, affineBlowUp_chart_appLE_awayToSection,
    reesAlgebra.chartRingEquiv_fromZeroRingHom]

theorem reesConstantSection_transition (a b : I) :
    reesConstantSection I (b : R) (Proj.basicOpen (reesAlgebra.grading I)
        (reesAlgebra.degreeOne I a) ⊓ Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I b)) =
      Proj.fracSection (reesAlgebra.grading I) (reesAlgebra.degreeOne_mem b)
        (reesAlgebra.degreeOne_mem a) _ inf_le_left * reesConstantSection I (a : R) _ := by
  unfold reesConstantSection
  rw [Proj.fracSection_mul]
  apply Proj.fracSection_eq
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_one, Subalgebra.coe_algebraMap,
    reesAlgebra.coe_degreeOne, Polynomial.algebraMap_eq]
  simp [mul_comm]

end MixedFujita
