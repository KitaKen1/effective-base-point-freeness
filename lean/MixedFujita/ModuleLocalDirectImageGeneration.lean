/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePushforwardGlobalSections

/-! 任意直像加群の局所生成元から元の点への反映。 See reports/check-243-base-locus-SNC-cut-basepoint-removal.json for the verified scope. Actual original Cartier base loci stabilize along powers. Stable-locus point removal for two coprime bases implies all large multiples generated. Usual KV lifts actual SNC-roundup cut generators and removes original basepoints. Usual KV and existence of required SNC data and cut generator remain explicit inputs; full klt BPF and F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- A map to an arbitrary direct image is locally multiplication by the pulled source
coefficient, even when the target frame exists only on a smaller source neighbourhood. -/
theorem moduleHomToPushforward_restricted_frame_coefficient
    {X Y : Scheme.{u}} (φ : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward φ).obj N) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (W : Y.Opens) (hWU : W ≤ φ ⁻¹ᵁ U)
    (d : N.over W ≅ SheafOfModules.unit (Y.ringCatSheaf.over W)) (s : Γ(M, U)) :
    moduleOverFrameCoefficient N W d W le_rfl
      (N.presheaf.map (homOfLE hWU).op (Scheme.Modules.Hom.app f U s)) =
      Y.presheaf.map (homOfLE hWU).op (φ.app U (moduleOverFrameCoefficient M U e U le_rfl s)) *
        moduleOverFrameCoefficient N W d W le_rfl
          (N.presheaf.map (homOfLE hWU).op (Scheme.Modules.Hom.app f U
            ((moduleOverFrameCoefficient M U e U le_rfl).symm 1))) := by
  let c := moduleOverFrameCoefficient M U e U le_rfl
  have hs : s = c s • c.symm 1 := by
    apply c.injective
    rw [LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  conv_lhs => rw [hs, Scheme.Modules.Hom.app_smul]
  change moduleOverFrameCoefficient N W d W le_rfl
    (N.val.map (homOfLE hWU).op
      (φ.app U (c s) • (show Γ(N, φ ⁻¹ᵁ U) from Scheme.Modules.Hom.app f U (c.symm 1)))) = _
  rw [N.val.map_smul, LinearEquiv.map_smul, smul_eq_mul]
  rfl


/-- A unit image coefficient on any source neighbourhood reflects a unit coefficient
at the original point. No target frame on the whole inverse image is required. -/
theorem moduleHomToPushforward_restricted_unit_reflects
    {X Y : Scheme.{u}} (φ : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward φ).obj N) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (W : Y.Opens) (hWU : W ≤ φ ⁻¹ᵁ U)
    (d : N.over W ≅ SheafOfModules.unit (Y.ringCatSheaf.over W))
    (y : Y) (hy : y ∈ W) (s : Γ(M, U))
    (hs : IsUnit (Y.presheaf.germ W y hy (moduleOverFrameCoefficient N W d W le_rfl
      (N.presheaf.map (homOfLE hWU).op (Scheme.Modules.Hom.app f U s))))) :
    IsUnit (X.presheaf.germ U (φ y) (hWU hy)
      (moduleOverFrameCoefficient M U e U le_rfl s)) := by
  rw [moduleHomToPushforward_restricted_frame_coefficient φ M N f U e W hWU d s,
    map_mul] at hs
  apply isUnit_of_map_unit (φ.stalkMap y).hom
  rw [Scheme.Hom.germ_stalkMap_apply]
  have hu := isUnit_of_mul_isUnit_left hs
  rw [Y.presheaf.germ_res_apply] at hu
  exact hu


/-- Actual global section surjectivity into ANY direct image reflects a generator
at an image point, even for nonreduced sources and unrelated target modules. -/
theorem module_source_generator_of_surjective_pushforward_at_point
    {X Y : Scheme.{u}} (φ : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (f : M ⟶ (Scheme.Modules.pushforward φ).obj N)
    (hf : Function.Surjective (Scheme.Modules.Hom.app f ⊤))
    (y : Y) (U : X.Opens) (hy : φ y ∈ U)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (W : Y.Opens) (hyW : y ∈ W)
    (d : N.over W ≅ SheafOfModules.unit (Y.ringCatSheaf.over W))
    (t : Γ(N, ⊤)) (ht : IsUnit (moduleOverFrameGlobalCoefficientGerm N W d y hyW t)) :
    ∃ s : Γ(M, ⊤), IsUnit (moduleOverFrameGlobalCoefficientGerm M U e (φ y) hy s) := by
  obtain ⟨s, hs⟩ := hf ((modulePushforwardGlobalSectionsAddEquiv φ N).symm t)
  have hst : modulePushforwardGlobalSectionsAddEquiv φ N (Scheme.Modules.Hom.app f ⊤ s) = t := by
    rw [hs, AddEquiv.apply_symm_apply]
  let V := W ⊓ φ ⁻¹ᵁ U
  have hyV : y ∈ V := ⟨hyW, hy⟩
  let dV := moduleOverFrameRestrictIso N W d V inf_le_left
  have htV : IsUnit (moduleOverFrameGlobalCoefficientGerm N V dV y hyV t) := by
    rwa [moduleOverFrameGlobalCoefficientGerm_restrict]
  apply Exists.intro s
  apply moduleHomToPushforward_restricted_unit_reflects φ M N f U e V inf_le_right dV y hyV
    (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s)
  have hrestrict : N.presheaf.map (homOfLE inf_le_right : V ⟶ φ ⁻¹ᵁ U).op
      (Scheme.Modules.Hom.app f U (M.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s)) =
      N.presheaf.map (homOfLE le_top : V ⟶ ⊤).op t := by
    rw [← moduleHomToPushforward_global_restrict φ M N f U s, hst]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [hrestrict]
  exact htV

end MixedFujita
