/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierIdealPowers
public import MixedFujita.CartierSectionLifting

/-! Identify the actual consecutive ideal-power inclusions with the natural
Cartier inclusions. This constructs a global Cartier cokernel presentation of
every actual infinitesimal layer from one equality of ideal sheaves. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
open TauCeti.AlgebraicGeometry.Scheme
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} [IsIntegral X]

@[reassoc (attr := simp)]
theorem cartierSheafEqToHom_inclusion {D F : CartierDivisor X} (h : D = F) :
    eqToHom (congrArg CartierDivisor.sheaf h) ≫ F.sheafι = D.sheafι := by
  subst F
  simp

theorem negativeCartierMultiple_succ (E : CartierDivisor X) (n : ℕ) :
    -((n + 1) • E) = -(n • E) - E := by
  rw [add_nsmul, one_nsmul]
  abel

noncomputable def cartierIdealPowerInclusion (E : CartierDivisor X)
    (hE : E.IsEffective) (n : ℕ) :
    (-((n + 1) • E)).sheaf ⟶ (-(n • E)).sheaf :=
  eqToHom (congrArg CartierDivisor.sheaf (negativeCartierMultiple_succ E n)) ≫
    cartierEffectiveInclusion (-(n • E)) E hE

@[reassoc (attr := simp)]
theorem cartierIdealPowerInclusion_toRationalFunctions (E : CartierDivisor X)
    (hE : E.IsEffective) (n : ℕ) :
    cartierIdealPowerInclusion E hE n ≫ (-(n • E)).sheafι =
      (-((n + 1) • E)).sheafι := by
  rw [cartierIdealPowerInclusion, Category.assoc, cartierEffectiveInclusion_ι,
    cartierSheafEqToHom_inclusion (negativeCartierMultiple_succ E n)]

theorem cartierIdealPowerInclusion_mono (E : CartierDivisor X)
    (hE : E.IsEffective) (n : ℕ) : Mono (cartierIdealPowerInclusion E hE n) :=
  mono_of_mono_fac (cartierIdealPowerInclusion_toRationalFunctions E hE n)

noncomputable def cartierIdealPowerModuleIso (E : CartierDivisor X)
    (hE : E.IsEffective) (J : X.IdealSheafData)
    (hJ : effectiveCartierIdealSheaf E hE = J) (n : ℕ) :
    (-(n • E)).sheaf ≅ idealSheafDataModule (J ^ n) := by
  subst J
  exact effectiveCartierIdealPowerModuleIso E hE n

@[reassoc (attr := simp)]
theorem cartierIdealPowerModuleIso_toRationalFunctions (E : CartierDivisor X)
    (hE : E.IsEffective) (J : X.IdealSheafData)
    (hJ : effectiveCartierIdealSheaf E hE = J) (n : ℕ) :
    (cartierIdealPowerModuleIso E hE J hJ n).hom ≫
        idealSheafDataModuleInclusion (J ^ n) ≫ toRationalFunctions X =
      (-(n • E)).sheafι := by
  subst J
  rw [cartierIdealPowerModuleIso, ← Category.assoc,
    effectiveCartierIdealPowerModuleIso_inclusion, negativeCartierToUnit_toRationalFunctions]

theorem cartierIdealPowerModuleIso_transition (E : CartierDivisor X)
    (hE : E.IsEffective) (J : X.IdealSheafData)
    (hJ : effectiveCartierIdealSheaf E hE = J) (n : ℕ) :
    cartierIdealPowerInclusion E hE n ≫ (cartierIdealPowerModuleIso E hE J hJ n).hom =
      (cartierIdealPowerModuleIso E hE J hJ (n + 1)).hom ≫
        idealSheafDataModuleMap (idealSheafPower_le_succ J n) := by
  apply (cancel_mono (idealSheafDataModuleInclusion (J ^ n) ≫ toRationalFunctions X)).mp
  simp only [Category.assoc, cartierIdealPowerModuleIso_toRationalFunctions,
    idealSheafDataModuleMap_inclusion_assoc, cartierIdealPowerInclusion_toRationalFunctions]

noncomputable def cartierIdealPowerCokernelIso (E : CartierDivisor X)
    (hE : E.IsEffective) (J : X.IdealSheafData)
    (hJ : effectiveCartierIdealSheaf E hE = J) (n : ℕ) :
    cokernel (cartierIdealPowerInclusion E hE n) ≅
      cokernel (idealSheafDataModuleMap (idealSheafPower_le_succ J n)) :=
  cokernel.mapIso _ _ (cartierIdealPowerModuleIso E hE J hJ (n + 1))
    (cartierIdealPowerModuleIso E hE J hJ n)
    (cartierIdealPowerModuleIso_transition E hE J hJ n)

noncomputable def infinitesimalLayerCartierCokernelIso {A : CommRingCat.{u}}
    [IsNoetherianRing A] (f : X ⟶ Spec A) (I : Ideal A)
    (E : CartierDivisor X) (hE : E.IsEffective)
    (hJ : effectiveCartierIdealSheaf E hE = infinitesimalBaseIdealSheaf f I) (n : ℕ) :
    infinitesimalCohomologyLayer f I (unitModule X) n ≅
      cokernel (cartierIdealPowerInclusion E hE (n + 1)) :=
  infinitesimalLayerIdealSheafQuotientIso f I n ≪≫
    (cartierIdealPowerCokernelIso E hE _ hJ (n + 1)).symm

end MixedFujita
