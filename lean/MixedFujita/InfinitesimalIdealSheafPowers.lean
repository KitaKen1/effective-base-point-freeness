/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalLayerIdealPowerQuotient
public import MixedFujita.QuasicoherentImageIdealSheaf
public import Hironaka.Scheme.BlowUp.InverseImage

/-! Compare the actual SGA powers with powers of the actual inverse-image
ideal sheaf. The comparison commutes with inclusions and gives a global
associated-graded presentation, without supplying degreewise isomorphisms. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) (I : Ideal A)

noncomputable def infinitesimalBaseIdealSheaf : X.IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso A).inv.hom)).comap f

theorem infinitesimalBaseIdealSheaf_affine (U : X.affineOpens) :
    (infinitesimalBaseIdealSheaf f I).ideal U = I.map (structMapV f U.1) := by
  rw [infinitesimalBaseIdealSheaf,
    Scheme.IdealSheafData.ideal_comap_of_le _ f ⟨⊤, isAffineOpen_top _⟩ U le_top,
    Scheme.IdealSheafData.ofIdealTop_ideal]
  simp only [show homOfLE (le_top : (⊤ : (Spec A).Opens) ≤ ⊤) = 𝟙 _ from rfl,
    op_id, Ideal.map_map]
  rfl

theorem infinitesimalBaseIdealSheaf_pow_affine (U : X.affineOpens) (n : ℕ) :
    ((infinitesimalBaseIdealSheaf f I) ^ n).ideal U =
      (I ^ n).map (structMapV f U.1) := by
  change ((infinitesimalBaseIdealSheaf f I).ideal U) ^ n = _
  rw [infinitesimalBaseIdealSheaf_affine, Ideal.map_pow]

theorem idealSheafPower_le_succ (J : X.IdealSheafData) (n : ℕ) : J ^ (n + 1) ≤ J ^ n := by
  intro U
  exact Ideal.pow_le_pow_right n.le_succ

noncomputable def quasicoherentImageIdealModuleIsoOfEq {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ unitModule X) [Mono φ] (J : X.IdealSheafData)
    (h : quasicoherentModuleImageIdealSheaf M φ = J) : M ≅ idealSheafDataModule J := by
  subst J
  exact quasicoherentImageIdealModuleIso φ

theorem quasicoherentImageIdealModuleIsoOfEq_inclusion {M : X.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ unitModule X) [Mono φ] (J : X.IdealSheafData)
    (h : quasicoherentModuleImageIdealSheaf M φ = J) :
    (quasicoherentImageIdealModuleIsoOfEq φ J h).hom ≫ idealSheafDataModuleInclusion J = φ := by
  subst J
  exact quasicoherentImageIdealModuleIso_hom_inclusion φ

variable [IsNoetherianRing A]

local instance (n : ℕ) : (IPow f I (unitModule X) n).IsQuasicoherent :=
  idealPower_isQuasicoherent f I (unitModule X) n

theorem idealPowerImageIdealSheaf_eq (n : ℕ) :
    quasicoherentModuleImageIdealSheaf (IPow f I (unitModule X) n)
        (ιPow f I (unitModule X) n) = (infinitesimalBaseIdealSheaf f I) ^ n := by
  apply Scheme.IdealSheafData.ext
  funext U
  apply SetLike.coe_injective
  ext x
  change x ∈ Set.range ((ιPow f I (unitModule X) n).app U.1) ↔ _
  rw [mem_range_ιPow_app f I (unitModule X) U.2,
    infinitesimalBaseIdealSheaf_pow_affine]
  simp only [Ideal.smul_eq_mul, Ideal.mul_top]
  rfl

noncomputable def idealPowerCanonicalModuleIso (n : ℕ) :
    IPow f I (unitModule X) n ≅
      idealSheafDataModule ((infinitesimalBaseIdealSheaf f I) ^ n) :=
  quasicoherentImageIdealModuleIsoOfEq (ιPow f I (unitModule X) n)
    ((infinitesimalBaseIdealSheaf f I) ^ n) (idealPowerImageIdealSheaf_eq f I n)

@[reassoc (attr := simp)]
theorem idealPowerCanonicalModuleIso_inclusion (n : ℕ) :
    (idealPowerCanonicalModuleIso f I n).hom ≫
        idealSheafDataModuleInclusion ((infinitesimalBaseIdealSheaf f I) ^ n) =
      ιPow f I (unitModule X) n :=
  quasicoherentImageIdealModuleIsoOfEq_inclusion _ _ _

theorem idealPowerCanonicalModuleIso_transition (n : ℕ) :
    inclPow f I (unitModule X) n.le_succ ≫ (idealPowerCanonicalModuleIso f I n).hom =
      (idealPowerCanonicalModuleIso f I (n + 1)).hom ≫
        idealSheafDataModuleMap (idealSheafPower_le_succ (infinitesimalBaseIdealSheaf f I) n) := by
  apply (cancel_mono (idealSheafDataModuleInclusion ((infinitesimalBaseIdealSheaf f I) ^ n))).mp
  simp only [Category.assoc, idealPowerCanonicalModuleIso_inclusion,
    idealSheafDataModuleMap_inclusion, inclPow_ιPow]

/-- The global layer is the actual quotient of two consecutive ideal-sheaf powers. -/
noncomputable def infinitesimalLayerIdealSheafQuotientIso (n : ℕ) :
    infinitesimalCohomologyLayer f I (unitModule X) n ≅
      cokernel (idealSheafDataModuleMap
        (idealSheafPower_le_succ (infinitesimalBaseIdealSheaf f I) (n + 1))) :=
  (infinitesimalLayerIdealPowerQuotientIso f I (unitModule X) n).symm ≪≫
    cokernel.mapIso _ _ (idealPowerCanonicalModuleIso f I (n + 1 + 1))
      (idealPowerCanonicalModuleIso f I (n + 1))
      (idealPowerCanonicalModuleIso_transition f I (n + 1))

end MixedFujita
