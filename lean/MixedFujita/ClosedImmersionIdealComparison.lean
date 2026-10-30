/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierCutQuotientTransport

/-! A closed immersion with the specified kernel identifies the actual
closed subscheme, compatibly with its ambient map and every open restriction. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (J : X.IdealSheafData) (p : Y ⟶ X) [IsClosedImmersion p]
  (hJ : p.ker = J)

noncomputable def idealSubschemeIsoOfClosedImmersion : J.subscheme ≅ Y := by
  have hker : J.subschemeι.ker = p.ker := (Scheme.IdealSheafData.ker_subschemeι J).trans hJ.symm
  have := IsClosedImmersion.isIso_lift J.subschemeι p hker
  exact (asIso (IsClosedImmersion.lift J.subschemeι p hker.le)).symm

@[reassoc (attr := simp)]
theorem idealSubschemeIsoOfClosedImmersion_inv_inclusion :
    (idealSubschemeIsoOfClosedImmersion J p hJ).inv ≫ J.subschemeι = p :=
  IsClosedImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem idealSubschemeIsoOfClosedImmersion_hom_immersion :
    (idealSubschemeIsoOfClosedImmersion J p hJ).hom ≫ p = J.subschemeι := by
  calc
    _ = (idealSubschemeIsoOfClosedImmersion J p hJ).hom ≫
        ((idealSubschemeIsoOfClosedImmersion J p hJ).inv ≫ J.subschemeι) :=
      congrArg (fun z => (idealSubschemeIsoOfClosedImmersion J p hJ).hom ≫ z)
        (idealSubschemeIsoOfClosedImmersion_inv_inclusion J p hJ).symm
    _ = _ := Iso.hom_inv_id_assoc _ _

theorem idealSubschemeIsoOfClosedImmersion_image_preimage (U : X.Opens) :
    (idealSubschemeIsoOfClosedImmersion J p hJ).hom ''ᵁ (J.subschemeι ⁻¹ᵁ U) = p ⁻¹ᵁ U := by
  rw [← Scheme.Hom.inv_preimage, ← Scheme.Hom.comp_preimage]
  rw [idealSubschemeIsoOfClosedImmersion_inv_inclusion]

noncomputable def idealSubschemePushforwardUnitIsoOfKernel :
    (Scheme.Modules.pushforward J.subschemeι).obj (SheafOfModules.unit J.subscheme.ringCatSheaf) ≅
      (Scheme.Modules.pushforward p).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  idealSubschemePushforwardUnitIsoOfIso J (idealSubschemeIsoOfClosedImmersion J p hJ) p
    (idealSubschemeIsoOfClosedImmersion_inv_inclusion J p hJ)

end MixedFujita
