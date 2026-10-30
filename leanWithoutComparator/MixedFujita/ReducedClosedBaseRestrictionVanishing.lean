/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ReducedInvertibleSectionGeneration
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! 被約閉部分源が完全基底集合内にあれば全射制限切断は零。 See reports/check-249-original-BPF-adjoint-all-multiples-stable-restriction.json for the verified scope. Original BPF positivity internally supplies all sufficiently large perturbed-adjoint nef-big conditions, with an explicit coarse natural degree bound. A fixed nonempty reduced W inside the complete base locus has usual-KV-based actual H1 vanishing and restriction surjectivity for every large original multiple. For a supplied stable nonempty power base and an actual initial seed, all high power restricted section spaces on W are zero. Initial and restricted-section nonvanishing, usual KV, klt BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

/-- Actual global restriction surjectivity to a REDUCED closed source contained
in the complete base locus forces ALL restricted sections to be zero. -/
theorem reduced_closed_base_locus_restriction_sections_subsingleton
    {X : Scheme.{u}} [IsIntegral X] (I : X.IdealSheafData) [IsReduced I.subscheme]
    (P : CartierDivisor X)
    (r : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf))
    (hr : Function.Surjective (Scheme.Modules.Hom.app r ⊤))
    (hplace : I.support ≤ cartierBaseLocus P) :
    Subsingleton Γ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf, ⊤) := by
  have hz (s : Γ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf, ⊤)) : s = 0 := by
    by_contra hs
    obtain ⟨y, hy⟩ := cartier_generator_at_image_of_nonzero_reduced_pullback_section I.subschemeι P r hr s hs
    have hmem : I.subschemeι y ∈ I.support := by
      change I.subschemeι y ∈ (I.support : Set X)
      rw [← I.range_subschemeι]
      exact ⟨y, rfl⟩
    have hB := hplace hmem
    change I.subschemeι y ∉ cartierGenerationOpen P at hB
    exact hB hy
  exact ⟨fun s t => (hz s).trans (hz t).symm⟩

end MixedFujita
