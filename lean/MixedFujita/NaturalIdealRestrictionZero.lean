/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealSheafModuleFunctor
public import MixedFujita.ModulePullbackSections
public import MixedFujita.GlobalCartierPullbackTensor
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! 実イデアル切断の自然制限零性と有限補正族の制限不変。 See reports/check-259-ample-ideal-generators-natural-corrections.json for the verified scope. All sufficiently high ORIGINAL ample Cartier twists of any actual coherent module are quotients of finite free sheaves, in every residue class. Actual noninvertible ideal modules are internally coherent and get finite canonical actual global generators. The canonical ideal inclusion pulls back to ZERO on its own actual closed subscheme by the actual adjunction mate. Arbitrary module tensor and NATURAL section restriction preserve this zero; finite ideal corrections preserve exact natural restriction and nonzero restricted sections even for nonreduced closed subschemes. Comparison of the finite ambient Cartier image family with center-exterior basepointfreeness, exterior LC/Bertini, ambient non-LC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000


/-- The canonical inclusion of ANY actual ideal module pulls back to ZERO on
its own actual closed subscheme. This is the mate of the actual kernel equation
under the actual pullback/pushforward adjunction; no flatness, reducedness,
integrality, normality or cohomology is required. -/
theorem idealSheafDataModuleInclusion_pullback_to_subscheme_zero
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    (Scheme.Modules.pullback I.subschemeι).map (idealSheafDataModuleInclusion I) = 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction I.subschemeι
  apply (cancel_mono (Scheme.Modules.pullbackObjUnitIso I.subschemeι).hom).mp
  rw [zero_comp]
  apply (adj.homEquiv _ _).injective
  have hu : adj.homEquiv (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit I.subscheme.ringCatSheaf)
      (Scheme.Modules.pullbackObjUnitIso I.subschemeι).hom =
        schemeUnitToPushforwardUnit I.subschemeι :=
    Scheme.Modules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom I.subschemeι
  rw [adj.homEquiv_naturality_left]
  exact ((congrArg (fun g => idealSheafDataModuleInclusion I ≫ g) hu).trans
    (kernel.condition (schemeUnitToPushforwardUnit I.subschemeι))).trans (adj.homAddEquiv_zero _ _).symm


/-- Tensoring an arbitrary actual module with the canonical ideal inclusion
still gives a map whose NATURAL pullback to that closed subscheme is zero.
This supplies exact natural restriction vanishing for ideal-generated sections. -/
theorem tensor_idealSheafDataModuleInclusion_pullback_to_subscheme_zero
    {X : Scheme.{u}} (P : X.Modules) (I : X.IdealSheafData) :
    (Scheme.Modules.pullback I.subschemeι).map
      (P ◁ idealSheafDataModuleInclusion I ≫ (ρ_ P).hom) = 0 := by
  let F := Scheme.Modules.pullback I.subschemeι
  let : MonoidalPreadditive I.subscheme.Modules := TauCeti.monoidalPreadditive_of_monoidalClosed _
  have hmap : F.map (P ◁ idealSheafDataModuleInclusion I) = 0 := by
    let : IsIso (Functor.OplaxMonoidal.δ F P (SheafOfModules.unit X.ringCatSheaf)) :=
      modulePullbackTensorComparison_isIso_of_right_frame I.subschemeι P _ (Iso.refl _)
    apply (cancel_mono (Functor.OplaxMonoidal.δ F P (SheafOfModules.unit X.ringCatSheaf))).mp
    rw [zero_comp]
    have h := Functor.OplaxMonoidal.δ_natural F (𝟙 P) (idealSheafDataModuleInclusion I)
    have hid : (𝟙 P ⊗ₘ idealSheafDataModuleInclusion I) = P ◁ idealSheafDataModuleInclusion I := by
      simp only [tensorHom_def, id_whiskerRight, Category.id_comp]
    rw [hid] at h
    have hi : F.map (idealSheafDataModuleInclusion I) = 0 :=
      idealSheafDataModuleInclusion_pullback_to_subscheme_zero I
    have hz : (F.map (𝟙 P) ⊗ₘ F.map (idealSheafDataModuleInclusion I)) = 0 := by
      rw [hi]
      exact MonoidalPreadditive.tensor_zero _
    exact h.symm.trans (by rw [hz, comp_zero])
  rw [Functor.map_comp, hmap, zero_comp]


/-- Every global section obtained from the ACTUAL twisted ideal has ZERO
NATURAL restriction to its closed subscheme. This holds on arbitrary schemes,
even for nonreduced or nonintegral closed subschemes. -/
theorem ideal_tensor_global_section_natural_restriction_zero
    {X : Scheme.{u}} (P : X.Modules) (I : X.IdealSheafData)
    (t : Γ(P ⊗ idealSheafDataModule I, ⊤)) :
    modulePullbackGlobalSections I.subschemeι P
      (Scheme.Modules.Hom.app (P ◁ idealSheafDataModuleInclusion I ≫ (ρ_ P).hom) ⊤ t) = 0 := by
  rw [modulePullbackGlobalSections_naturality,
    tensor_idealSheafDataModuleInclusion_pullback_to_subscheme_zero]
  rfl


/-- Add ANY finite linear combination of actual twisted-ideal global sections
to a fixed ambient section. Its NATURAL restriction is unchanged; a nonzero
original natural restriction guarantees that every corrected ambient section
is nonzero. Coefficients are actual global regular functions, including base
field constants when present. -/
theorem ideal_finite_global_corrections_preserve_natural_restriction_and_nonzero
    {X : Scheme.{u}} (P : X.Modules) (I : X.IdealSheafData)
    (s : Γ(P, ⊤)) (hres : modulePullbackGlobalSections I.subschemeι P s ≠ 0)
    {J : Type*} [Fintype J] (g : J → Γ(P ⊗ idealSheafDataModule I, ⊤))
    (c : J → Γ(X, ⊤)) :
    let s' := s + Scheme.Modules.Hom.app
      (P ◁ idealSheafDataModuleInclusion I ≫ (ρ_ P).hom) ⊤ (∑ i, c i • g i)
    modulePullbackGlobalSections I.subschemeι P s' = modulePullbackGlobalSections I.subschemeι P s ∧ s' ≠ 0 := by
  dsimp only
  have heq : modulePullbackGlobalSections I.subschemeι P
      (s + Scheme.Modules.Hom.app (P ◁ idealSheafDataModuleInclusion I ≫ (ρ_ P).hom) ⊤
        (∑ i, c i • g i)) = modulePullbackGlobalSections I.subschemeι P s := by
    rw [map_add, ideal_tensor_global_section_natural_restriction_zero, add_zero]
  refine ⟨heq, ?_⟩
  intro hz
  apply hres
  rw [← heq, hz, map_zero]

end MixedFujita
