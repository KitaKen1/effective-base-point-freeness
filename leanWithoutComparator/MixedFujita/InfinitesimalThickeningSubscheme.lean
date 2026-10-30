/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalIdealSheafPowers

/-! The actual infinitesimal quotient is the pushforward of the structure
sheaf of the actual closed thickening. The isomorphism is constructed from
the two cokernel universal properties and respects the quotient morphism. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A : CommRingCat.{u}} [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A) (I : Ideal A)

noncomputable def idealPowerCokernelQuotientIso (M : X.Modules) (n : ℕ) :
    cokernel (ιPow f I M (n + 1)) ≅ M.quotientIdealPow f I n :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (shortExact_quotientIdealPow f I M n).gIsCokernel

@[reassoc (attr := simp)]
theorem idealPowerCokernelQuotientIso_π (M : X.Modules) (n : ℕ) :
    cokernel.π (ιPow f I M (n + 1)) ≫ (idealPowerCokernelQuotientIso f I M n).hom =
      M.toQuotientIdealPow f I n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (shortExact_quotientIdealPow f I M n).gIsCokernel WalkingParallelPair.one

noncomputable def idealSheafModuleCokernelIso (J : X.IdealSheafData) :
    cokernel (idealSheafDataModuleInclusion J) ≅
      (Scheme.Modules.pushforward J.subschemeι).obj (unitModule J.subscheme) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (idealSheafDataModuleQuotientSequence_shortExact J).gIsCokernel

@[reassoc (attr := simp)]
theorem idealSheafModuleCokernelIso_π (J : X.IdealSheafData) :
    cokernel.π (idealSheafDataModuleInclusion J) ≫ (idealSheafModuleCokernelIso J).hom =
      schemeUnitToPushforwardUnit J.subschemeι :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (idealSheafDataModuleQuotientSequence_shortExact J).gIsCokernel WalkingParallelPair.one

/-- A global sheaf isomorphism with the actual nonreduced closed thickening. -/
noncomputable def infinitesimalQuotientIdealSubschemeIso (n : ℕ) :
    (unitModule X).quotientIdealPow f I n ≅
      (Scheme.Modules.pushforward ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subschemeι).obj
        (unitModule ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subscheme) :=
  (idealPowerCokernelQuotientIso f I (unitModule X) n).symm ≪≫
    cokernel.mapIso _ _ (idealPowerCanonicalModuleIso f I (n + 1)) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.comp_id] using
        (idealPowerCanonicalModuleIso_inclusion f I (n + 1)).symm) ≪≫
    idealSheafModuleCokernelIso _

@[reassoc]
theorem infinitesimalQuotientIdealSubschemeIso_quotient (n : ℕ) :
    (unitModule X).toQuotientIdealPow f I n ≫
        (infinitesimalQuotientIdealSubschemeIso f I n).hom =
      schemeUnitToPushforwardUnit ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subschemeι := by
  rw [← idealPowerCokernelQuotientIso_π f I (unitModule X) n]
  simp only [infinitesimalQuotientIdealSubschemeIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc_assoc,
    Iso.refl_hom, Category.id_comp, idealSheafModuleCokernelIso_π]

end MixedFujita
