/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineBlowupReesSections
public import MixedFujita.AffineIdealSheaves

/-! Actual Rees sections, exceptional ideals and all integer twisting modules
under a coefficient map carrying the center ideal onto its extension. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type u} [CommRing R] [CommRing S]
  {I : Ideal R} {J : Ideal S} (φ : R →+* S) (hJ : I.map φ = J)

theorem affineBlowUp_mapOfEq_exceptionalIdeal :
    (affineBlowUp.exceptionalIdeal I).comap (affineBlowUp.mapOfEq φ hJ) =
      affineBlowUp.exceptionalIdeal J := by
  change ((specIdealSheaf I).comap (affineBlowUp.π I)).comap _ =
    (specIdealSheaf J).comap (affineBlowUp.π J)
  rw [← Scheme.IdealSheafData.comap_comp, affineBlowUp.mapOfEq_π,
    Scheme.IdealSheafData.comap_comp, specIdealSheaf_comap, hJ]

noncomputable def affineBlowUpExceptionalBaseChangeIso :
    (affineBlowUp.exceptionalIdeal J).subscheme ≅
      Limits.pullback (affineBlowUp.mapOfEq φ hJ)
        (affineBlowUp.exceptionalIdeal I).subschemeι :=
  idealSheafPullbackIso _ _ _ (affineBlowUp_mapOfEq_exceptionalIdeal φ hJ)

theorem affineBlowUpExceptionalBaseChangeIso_hom_fst :
    (affineBlowUpExceptionalBaseChangeIso φ hJ).hom ≫ Limits.pullback.fst _ _ =
      (affineBlowUp.exceptionalIdeal J).subschemeι :=
  idealSheafPullbackIso_hom_fst _ _ _ (affineBlowUp_mapOfEq_exceptionalIdeal φ hJ)

theorem affineBlowUp_mapOfEq_constant (r : R)
    (U : (affineBlowUp I).Opens) (V : (affineBlowUp J).Opens)
    (hV : V ≤ affineBlowUp.mapOfEq φ hJ ⁻¹ᵁ U) :
    (affineBlowUp.mapOfEq φ hJ).appLE U V hV (reesConstantSection I r U) =
      reesConstantSection J (φ r) V := by
  dsimp only [affineBlowUp.mapOfEq] at hV ⊢
  rw [reesConstantSection, projMap_appLE_fracSection]
  have hc : reesAlgebra.mapOfLe φ hJ.le (algebraMap R (reesAlgebra I) r) =
      algebraMap S (reesAlgebra J) (φ r) := by
    apply Subtype.ext
    simp [reesAlgebra.coe_mapOfLe_apply, Polynomial.algebraMap_eq]
  simp only [hc, map_one, reesConstantSection]

variable {ι : Type u} (a : ι → I)
  (hcov : ⨆ i, Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I (a i)) = ⊤)

include hcov in
theorem reesBaseChange_degreeOne_cover :
    ⨆ i, Proj.basicOpen (reesAlgebra.grading J)
      (reesAlgebra.degreeOne J ⟨φ (a i), hJ.le (Ideal.mem_map_of_mem φ (a i).2)⟩) = ⊤ := by
  simpa only [reesAlgebra.mapOfLe_degreeOne] using
    projMap_image_degreeOne_cover (reesAlgebra.mapOfLe φ hJ.le)
      (reesAlgebra.irrelevant_le_map_mapOfEq φ hJ)
      (fun i => reesAlgebra.degreeOne I (a i)) hcov

theorem reesTwistingSheaf_baseChange :
    (Proj.twistingSheaf (reesAlgebra.grading I) (fun i => reesAlgebra.degreeOne I (a i))
      (fun i => reesAlgebra.degreeOne_mem (a i)) hcov).pullback
        (affineBlowUp.mapOfEq φ hJ) =
    Proj.twistingSheaf (reesAlgebra.grading J)
      (fun i => reesAlgebra.degreeOne J ⟨φ (a i), hJ.le (Ideal.mem_map_of_mem φ (a i).2)⟩)
      (fun _ => reesAlgebra.degreeOne_mem _)
      (reesBaseChange_degreeOne_cover φ hJ a hcov) := by
  rw [affineBlowUp.mapOfEq, projTwistingSheaf_pullback]
  congr 1
  funext i
  exact reesAlgebra.mapOfLe_degreeOne φ hJ.le (a i)

noncomputable def reesTwistingModuleBaseChangeIso (d : ℤ) :
    (Scheme.Modules.pullback (affineBlowUp.mapOfEq φ hJ)).obj
      ((Proj.twistingSheaf (reesAlgebra.grading I) (fun i => reesAlgebra.degreeOne I (a i))
        (fun i => reesAlgebra.degreeOne_mem (a i)) hcov).toModules d) ≅
    (Proj.twistingSheaf (reesAlgebra.grading J)
      (fun i => reesAlgebra.degreeOne J ⟨φ (a i), hJ.le (Ideal.mem_map_of_mem φ (a i).2)⟩)
      (fun _ => reesAlgebra.degreeOne_mem _)
      (reesBaseChange_degreeOne_cover φ hJ a hcov)).toModules d :=
  sgaLineBundlePullbackPowerIso _ _ d ≪≫
    eqToIso (congrArg (fun L => L.toModules d) (reesTwistingSheaf_baseChange φ hJ a hcov))

end MixedFujita
