/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealSheafComapModuleEpimorphism

/-! 実イデアルの空台同型と中心外sourceへの自然pullback全射。 See reports/check-260-ideal-exterior-affine-generation.json for the verified scope. Actual quasicoherent epimorphisms are surjective on every affine open; the SAME finite global generators span there and have a unit coefficient at any specified affine frame. Empty actual ideal support gives an isomorphic inclusion; the nonflat actual comap comparison makes natural ideal inclusion and Cartier-twisted inclusion epimorphic after mapping off support. ALL high original ample powers construct one finite actual ambient Cartier family naturally zero on the actual closed center whose canonical finite-free map pulls back epimorphically on its canonical open complement. Identifying this with the canonical map of the same naturally pulled global sections, pointwise original Cartier basepointfreeness, exterior LC/Bertini, ambient nonLC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- The actual ideal inclusion is an isomorphism if its actual support is
empty, on an arbitrary scheme. This uses the original affine ideal image. -/
theorem idealSheafDataModuleInclusion_isIso_of_support_empty
    {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.support = ⊥) :
    IsIso (idealSheafDataModuleInclusion I) := by
  have htop : I = ⊤ := (Scheme.IdealSheafData.support_eq_bot_iff I).mp hI
  have hepi : Epi (idealSheafDataModuleInclusion I) := by
    apply moduleHom_epi_of_affine_app_surjective
    intro U r
    have hr : r ∈ I.ideal U := by rw [htop]; trivial
    exact (Set.ext_iff.mp (idealSheafDataModuleInclusion_affine_image I U) r).mpr hr
  let := hepi
  exact isIso_of_mono_of_epi _


/-- If an actual source maps outside the original ideal support, the NATURAL
pullback of the actual ideal inclusion is an epimorphism. The arbitrary
nonflat comap comparison is used; no ideal invertibility is assumed. -/
theorem idealSheafDataModuleInclusion_pullback_epi_off_support
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (φ : Y ⟶ X)
    (havoid : ∀ y : Y, φ y ∉ I.support) :
    Epi ((Scheme.Modules.pullback φ).map (idealSheafDataModuleInclusion I)) := by
  have hsupp : (I.comap φ).support = ⊥ := by
    rw [Scheme.IdealSheafData.support_comap]
    ext y
    change (φ y ∈ I.support) ↔ False
    exact iff_false_intro (havoid y)
  let : IsIso (idealSheafDataModuleInclusion (I.comap φ)) :=
    idealSheafDataModuleInclusion_isIso_of_support_empty (I.comap φ) hsupp
  let : Epi (idealSheafComapModuleMap I φ) := idealSheafComapModuleMap_epi I φ
  have hfac := idealSheafComapModuleMap_inclusion I φ
  change idealSheafComapModuleMap I φ ≫ idealSheafDataModuleInclusion (I.comap φ) =
    (Scheme.Modules.pullback φ).map (idealSheafDataModuleInclusion I) ≫
      (Scheme.Modules.pullbackObjUnitIso φ).hom at hfac
  have heq : (Scheme.Modules.pullback φ).map (idealSheafDataModuleInclusion I) =
      (idealSheafComapModuleMap I φ ≫ idealSheafDataModuleInclusion (I.comap φ)) ≫
        (Scheme.Modules.pullbackObjUnitIso φ).inv := by
    rw [hfac, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

end MixedFujita
