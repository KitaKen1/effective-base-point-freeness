/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineBlowupFlatReesBaseChange
public import MixedFujita.CoordinateExceptionalConormal
public import Mathlib.RingTheory.Flat.TorsionFree

/-! The actual exceptional subscheme and conormal after coordinate base change.
The pulled projective bundle supplies every infinitesimal layer. The statements
do not presuppose a Cartier divisor or degreewise layer identifications. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme CoordinateSubspace CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n)
  {S : Type u} [CommRing S] (φ : MvPolynomial (Fin n) A →+* S)
noncomputable local instance coordinateBaseChangeCenterCommRing :
    CommRing (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) := Ideal.Quotient.commRing _

noncomputable def coordinateBaseChangedReesBundle :
    (affineBlowUp ((centerIdeal A n r).map φ)).LineBundle :=
  Proj.twistingSheaf (reesAlgebra.grading ((centerIdeal A n r).map φ))
    (fun i : ULift.{u} (Fin r) => reesAlgebra.degreeOne ((centerIdeal A n r).map φ)
      ⟨φ (genXOfFin A n r hrn i.down), Ideal.mem_map_of_mem φ (genXOfFin A n r hrn i.down).2⟩)
    (fun _ => reesAlgebra.degreeOne_mem _)
    (reesBaseChange_degreeOne_cover φ rfl
      (fun i : ULift.{u} (Fin r) => genXOfFin A n r hrn i.down)
      (coordinateRees_degreeOne_cover A n r hrn))

noncomputable def coordinateExceptionalBaseChangedScheme : Scheme.{u} :=
  pullback (affineBlowUp.mapOfEq φ (I := centerIdeal A n r) rfl) (projInitial A n r hrn)

noncomputable def coordinateExceptionalBaseChangedInclusion :
    coordinateExceptionalBaseChangedScheme A n r hrn φ ⟶
      affineBlowUp ((centerIdeal A n r).map φ) := pullback.fst _ _

noncomputable def coordinateExceptionalBaseChangedProjection :
    coordinateExceptionalBaseChangedScheme A n r hrn φ ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin r)
        (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)) := pullback.snd _ _

instance coordinateExceptionalBaseChangedInclusion_isClosedImmersion :
    IsClosedImmersion (coordinateExceptionalBaseChangedInclusion A n r hrn φ) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst _ (projInitial A n r hrn)))

theorem coordinateExceptionalBaseChangedInclusion_ker :
    (coordinateExceptionalBaseChangedInclusion A n r hrn φ).ker =
      affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ) := by
  rw [coordinateExceptionalBaseChangedInclusion,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ker_projInitial,
    affineBlowUp_mapOfEq_exceptionalIdeal]

noncomputable def coordinateExceptionalBaseChangedIso :
    (affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ)).subscheme ≅
      coordinateExceptionalBaseChangedScheme A n r hrn φ :=
  idealSubschemeIsoOfClosedImmersion _ _ (coordinateExceptionalBaseChangedInclusion_ker A n r hrn φ)

theorem coordinateExceptionalBaseChangedIso_inv_inclusion :
    (coordinateExceptionalBaseChangedIso A n r hrn φ).inv ≫
        (affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ)).subschemeι =
      coordinateExceptionalBaseChangedInclusion A n r hrn φ :=
  idealSubschemeIsoOfClosedImmersion_inv_inclusion _ _
    (coordinateExceptionalBaseChangedInclusion_ker A n r hrn φ)

noncomputable def coordinateBaseChangedReesRestrictionIso (d : ℤ) :
    (Scheme.Modules.pullback (coordinateExceptionalBaseChangedInclusion A n r hrn φ)).obj
        ((coordinateBaseChangedReesBundle A n r hrn φ).toModules d) ≅
      (Scheme.Modules.pullback (coordinateExceptionalBaseChangedProjection A n r hrn φ)).obj
        (projectiveSpace.twist (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) d) := by
  let f := affineBlowUp.mapOfEq φ (I := centerIdeal A n r) rfl
  let p := coordinateExceptionalBaseChangedInclusion A n r hrn φ
  let q := coordinateExceptionalBaseChangedProjection A n r hrn φ
  let M := (coordinateReesTwistingBundle A n r hrn).toModules d
  have hc : p ≫ f = q ≫ projInitial A n r hrn := pullback.condition
  exact (Scheme.Modules.pullback p).mapIso
      (reesTwistingModuleBaseChangeIso φ rfl
        (fun i : ULift.{u} (Fin r) => genXOfFin A n r hrn i.down)
        (coordinateRees_degreeOne_cover A n r hrn) d).symm ≪≫
    (Scheme.Modules.pullbackComp p f).app M ≪≫
    eqToIso (congrArg (fun t => (Scheme.Modules.pullback t).obj M) hc) ≪≫
    ((Scheme.Modules.pullbackComp q (projInitial A n r hrn)).app M).symm ≪≫
    (Scheme.Modules.pullback q).mapIso (coordinateReesTwistingModuleRestrictionIso A n r hrn d)

variable [IsDomain A] [IsDomain S] (hr : 0 < r) (hφ : φ.Flat)

include hφ in
theorem coordinateBaseChange_injective : Function.Injective φ := by
  letI := φ.toAlgebra
  have : Module.Flat (MvPolynomial (Fin n) A) S :=
    (RingHom.flat_algebraMap_iff (R := MvPolynomial (Fin n) A) (S := S)).mp hφ
  exact FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) A) S

include hrn hr hφ in
theorem coordinateBaseChanged_center_ne_bot : (centerIdeal A n r).map φ ≠ ⊥ := by
  intro h
  have hx := Ideal.mem_map_of_mem φ (genXOfFin A n r hrn ⟨0, hr⟩).2
  rw [h, Ideal.mem_bot] at hx
  exact MvPolynomial.X_ne_zero _
    ((coordinateBaseChange_injective A n φ hφ) (hx.trans (map_zero φ).symm))

include hr hφ in
theorem coordinateBaseChanged_exists_cartier_conormal :
    let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n r).map φ)
      (coordinateBaseChanged_center_ne_bot A n r hrn φ hr hφ)
    ∃ (E : CartierDivisor (affineBlowUp ((centerIdeal A n r).map φ))) (hE : E.IsEffective),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ) ∧
      Nonempty ((-E).sheaf ≅ (coordinateBaseChangedReesBundle A n r hrn φ).toModules 1) ∧
      Nonempty
        ((Scheme.Modules.pullback (coordinateExceptionalBaseChangedInclusion A n r hrn φ)).obj
          (-E).sheaf ≅
          ((projectiveSpace.twistingBundle (Fin r)
            (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)).pullback
              (coordinateExceptionalBaseChangedProjection A n r hrn φ)).toModules 1) := by
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n r).map φ)
    (coordinateBaseChanged_center_ne_bot A n r hrn φ hr hφ)
  let : Nonempty (ULift.{u} (Fin r)) := ⟨⟨⟨0, hr⟩⟩⟩
  obtain ⟨E, hE, hI, ⟨e⟩⟩ := exists_exceptionalCartier_reesTwisting
    ((centerIdeal A n r).map φ)
    (fun i : ULift.{u} (Fin r) =>
      ⟨φ (genXOfFin A n r hrn i.down), Ideal.mem_map_of_mem φ (genXOfFin A n r hrn i.down).2⟩)
    (fun i h => MvPolynomial.X_ne_zero _
      ((coordinateBaseChange_injective A n φ hφ) (h.trans (map_zero φ).symm)))
    (reesBaseChange_degreeOne_cover φ rfl
      (fun i : ULift.{u} (Fin r) => genXOfFin A n r hrn i.down)
      (coordinateRees_degreeOne_cover A n r hrn))
  refine ⟨E, hE, hI, ⟨e⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.pullback (coordinateExceptionalBaseChangedInclusion A n r hrn φ)).mapIso e ≪≫
    coordinateBaseChangedReesRestrictionIso A n r hrn φ 1 ≪≫ sgaLineBundlePullbackPowerIso _ _ 1

include hr hφ in
theorem coordinateBaseChanged_infinitesimal_layers [IsNoetherianRing S] (m : ℕ) :
    Nonempty
      (infinitesimalCohomologyLayer (affineBlowUp.π ((centerIdeal A n r).map φ))
        ((centerIdeal A n r).map φ) (unitModule (affineBlowUp ((centerIdeal A n r).map φ))) m ≅
      (Scheme.Modules.pushforward (coordinateExceptionalBaseChangedInclusion A n r hrn φ)).obj
        (((projectiveSpace.twistingBundle (Fin r)
          (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)).pullback
          (coordinateExceptionalBaseChangedProjection A n r hrn φ)).toModules ((m : ℤ) + 1))) := by
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n r).map φ)
    (coordinateBaseChanged_center_ne_bot A n r hrn φ hr hφ)
  obtain ⟨E, hE, hI, -, ⟨a⟩⟩ :=
    coordinateBaseChanged_exists_cartier_conormal A n r hrn φ hr hφ
  let p := coordinateExceptionalBaseChangedInclusion A n r hrn φ
  let e := idealSubschemeIsoOfClosedImmersion (effectiveCartierIdealSheaf E hE) p
    ((coordinateExceptionalBaseChangedInclusion_ker A n r hrn φ).trans hI.symm)
  have hp := idealSubschemeIsoOfClosedImmersion_inv_inclusion (effectiveCartierIdealSheaf E hE) p
    ((coordinateExceptionalBaseChangedInclusion_ker A n r hrn φ).trans hI.symm)
  exact ⟨infinitesimalLayerLineBundlePowerIso _ _ E hE hI e p hp _ a m⟩

end MixedFujita
