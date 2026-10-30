/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleIdealGlobalGenerators
public import MixedFujita.NaturalIdealRestrictionZero
public import MixedFujita.FiniteGlobalAffineGeneration
public import MixedFujita.CartierIdealExteriorEpimorphism

/-! 同じ元ample有限切断族の中心上零性と開補集合有限自由全射。 See reports/check-260-ideal-exterior-affine-generation.json for the verified scope. Actual quasicoherent epimorphisms are surjective on every affine open; the SAME finite global generators span there and have a unit coefficient at any specified affine frame. Empty actual ideal support gives an isomorphic inclusion; the nonflat actual comap comparison makes natural ideal inclusion and Cartier-twisted inclusion epimorphic after mapping off support. ALL high original ample powers construct one finite actual ambient Cartier family naturally zero on the actual closed center whose canonical finite-free map pulls back epimorphically on its canonical open complement. Identifying this with the canonical map of the same naturally pulled global sections, pointwise original Cartier basepointfreeness, exterior LC/Bertini, ambient nonLC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- ALL high original ample twists have a finite actual ambient Cartier
section family which is NATURALLY ZERO on the actual closed subscheme and
whose canonical finite-free map is an EPIMORPHISM on its actual open complement.
The SAME global family is used on both pieces; its ideal coherence and
finite generation are internal. Pointwise unit-frame/Bertini control is not
asserted in this module-level generation statement. -/
theorem ample_ideal_sections_natural_zero_and_complement_finite_free_epi
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) (I : X.IdealSheafData) :
    let U : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∃ (k : ℕ) (s : Fin k → Γ((b • A).sheaf, ⊤)),
      (∀ i, modulePullbackGlobalSections I.subschemeι (b • A).sheaf (s i) = 0) ∧
      Epi ((modulePullbackUnitBiproductIso U.ι k).inv ≫
        (Scheme.Modules.pullback U.ι).map
          (biproduct.desc (fun i => CohomologyAux.homOfSection (b • A).sheaf (s i)))) := by
  classical
  let U : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  obtain ⟨b₀, hb₀⟩ := locallyNoetherian_ideal_all_high_ample_twists_finite_global_generators A hA I
  refine ⟨b₀, fun b hb => ?_⟩
  obtain ⟨k, g, hg⟩ := hb₀ b hb
  let := hg
  let P := (b • A).sheaf
  let δ : P ⊗ idealSheafDataModule I ⟶ P := P ◁ idealSheafDataModuleInclusion I ≫ (ρ_ P).hom
  let π := biproduct.desc (fun i => CohomologyAux.homOfSection (P ⊗ idealSheafDataModule I) (g i))
  let s (i : Fin k) := Scheme.Modules.Hom.app δ ⊤ (g i)
  have hdesc : biproduct.desc (fun i => CohomologyAux.homOfSection P (s i)) = π ≫ δ := by
    apply biproduct.hom_ext'
    intro i
    rw [biproduct.ι_desc, ← Category.assoc, biproduct.ι_desc]
    exact (homOfSection_comp_module_hom δ (g i)).symm
  have havoid (y : U) : U.ι y ∉ I.support := y.2
  let : Epi ((Scheme.Modules.pullback U.ι).map δ) :=
    cartier_tensor_ideal_inclusion_pullback_epi_off_support (b • A) I U.ι havoid
  let : Epi ((Scheme.Modules.pullback U.ι).map π) := (Scheme.Modules.pullback U.ι).map_epi π
  refine ⟨k, s, fun i => ideal_tensor_global_section_natural_restriction_zero P I (g i), ?_⟩
  rw [hdesc, Functor.map_comp]
  infer_instance

end MixedFujita
