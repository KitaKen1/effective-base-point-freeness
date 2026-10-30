/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealPullbackExteriorEpimorphism
public import MixedFujita.GlobalCartierPullbackTensor
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-! 中心外の実Cartier捻りイデアル自然pullback全射。 See reports/check-260-ideal-exterior-affine-generation.json for the verified scope. Actual quasicoherent epimorphisms are surjective on every affine open; the SAME finite global generators span there and have a unit coefficient at any specified affine frame. Empty actual ideal support gives an isomorphic inclusion; the nonflat actual comap comparison makes natural ideal inclusion and Cartier-twisted inclusion epimorphic after mapping off support. ALL high original ample powers construct one finite actual ambient Cartier family naturally zero on the actual closed center whose canonical finite-free map pulls back epimorphically on its canonical open complement. Identifying this with the canonical map of the same naturally pulled global sections, pointwise original Cartier basepointfreeness, exterior LC/Bertini, ambient nonLC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- After mapping outside the actual ideal support, the NATURAL pullback of
an actual Cartier-twisted ideal inclusion surjects onto the pulled Cartier
line. Both tensor comparisons are the actual Cartier comparisons. -/
theorem cartier_tensor_ideal_inclusion_pullback_epi_off_support
    {X Y : Scheme.{u}} [IsIntegral X] (P : CartierDivisor X)
    (I : X.IdealSheafData) (φ : Y ⟶ X) (havoid : ∀ y : Y, φ y ∉ I.support) :
    Epi ((Scheme.Modules.pullback φ).map
      (P.sheaf ◁ idealSheafDataModuleInclusion I ≫ (ρ_ P.sheaf).hom)) := by
  let F := Scheme.Modules.pullback φ
  let : Epi (F.map (idealSheafDataModuleInclusion I)) :=
    idealSheafDataModuleInclusion_pullback_epi_off_support I φ havoid
  have htensor : Epi (F.obj P.sheaf ◁ F.map (idealSheafDataModuleInclusion I)) :=
    (tensorLeft (F.obj P.sheaf)).map_epi _
  let := htensor
  let a := cartierPullbackTensorIso P φ (idealSheafDataModule I)
  let b := cartierPullbackTensorIso P φ (SheafOfModules.unit X.ringCatSheaf)
  have hfac : F.map (P.sheaf ◁ idealSheafDataModuleInclusion I) =
      a.hom ≫ (F.obj P.sheaf ◁ F.map (idealSheafDataModuleInclusion I)) ≫ b.inv := by
    apply (cancel_mono b.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h := Functor.OplaxMonoidal.δ_natural F (𝟙 P.sheaf) (idealSheafDataModuleInclusion I)
    have hid : (𝟙 P.sheaf ⊗ₘ idealSheafDataModuleInclusion I) = P.sheaf ◁ idealSheafDataModuleInclusion I := by
      simp only [tensorHom_def, id_whiskerRight, Category.id_comp]
    rw [hid] at h
    have hidF : F.map (𝟙 P.sheaf) = 𝟙 (F.obj P.sheaf) := F.map_id _
    have hmid : (F.map (𝟙 P.sheaf) ⊗ₘ F.map (idealSheafDataModuleInclusion I)) =
        F.obj P.sheaf ◁ F.map (idealSheafDataModuleInclusion I) := by
      rw [hidF]
      simp only [tensorHom_def, id_whiskerRight, Category.id_comp]
    rw [hmid] at h
    simpa only [a, b, cartierPullbackTensorIso_hom] using h.symm
  rw [Functor.map_comp, hfac]
  infer_instance

end MixedFujita
