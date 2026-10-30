/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.QuasicoherentImageIdealSheaf

/-! 実イデアル層の台の補集合と局所単位切断。 See reports/check-247-lc-non-klt-support-canonical-subscheme.json for the verified scope. The actual lc kernel image support equals the original all-model non-klt locus. Its radical coherent ideal and nonempty reduced lower-dimensional W are unique, independent of the SNC model and adjoint P, and constructed without KV. Containment in any closed Z is equivalent to klt outside Z. Usual KV is a condition only for simultaneous restriction lifting. Stable-base-locus perturbation, restricted-section nonvanishing, usual KV, normal minimal-lc-center adjunction, klt BPF and full F1/F2 remain unproved. -/

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

/-- An actual ideal sheaf misses a point precisely when it contains the unit
on some affine neighbourhood. Basic-open localization constructs that neighbourhood. -/
theorem idealSheaf_notMem_support_iff_affine_unit
    {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    x ∉ (I.support : Set X) ↔ ∃ U : X.affineOpens, x ∈ U.1 ∧ (1 : Γ(X, U.1)) ∈ I.ideal U := by
  classical
  constructor
  · intro hx
    have hn : ¬ ∀ U : X.affineOpens, x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
      fun h => hx (I.mem_support_iff.mpr h)
    push Not at hn
    obtain ⟨U, hU⟩ := hn
    rw [Scheme.mem_zeroLocus_iff] at hU
    push Not at hU
    obtain ⟨f, hf, hxf⟩ := hU
    let V := X.affineBasicOpen f
    have hm : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f ∈ I.ideal V := by
      rw [← I.map_ideal (X.basicOpen_le f)]
      exact Ideal.mem_map_of_mem _ hf
    have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) := by
      let := U.2.isLocalization_basicOpen f
      exact IsLocalization.Away.algebraMap_isUnit f
    refine ⟨V, hxf, ?_⟩
    rw [(I.ideal V).eq_top_of_isUnit_mem hm hu]
    trivial
  · rintro ⟨U, hxU, h1⟩ hx
    have hz := (I.mem_support_iff_of_mem hxU).mp hx
    have hn := (X.mem_zeroLocus_iff _ x).mp hz 1 h1
    exact hn (by simpa only [Scheme.basicOpen_one] using hxU)


/-- The complement of the actual quasicoherent image-ideal support is exactly the
locus where the ACTUAL map has a unit section on a neighbourhood. No monicity is needed. -/
theorem quasicoherentImageIdeal_notMem_support_iff_local_unit
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    x ∉ ((quasicoherentModuleImageIdealSheaf M j).support : Set X) ↔
      ∃ U : X.Opens, x ∈ U ∧ ∃ s : Γ(M, U), Scheme.Modules.Hom.app j U s = (1 : Γ(X, U)) := by
  constructor
  · intro hx
    obtain ⟨U, hxU, hs⟩ := (idealSheaf_notMem_support_iff_affine_unit _ x).mp hx
    exact ⟨U.1, hxU, hs⟩
  · rintro ⟨U, hxU, s, hs⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    apply (idealSheaf_notMem_support_iff_affine_unit _ x).mpr
    refine ⟨⟨V, hV⟩, hxV, M.presheaf.map (homOfLE hVU).op s, ?_⟩
    change Scheme.Modules.Hom.app j V (M.presheaf.map (homOfLE hVU).op s) = (1 : Γ(X, V))
    exact (moduleStructureHom_restriction j hVU s).trans
      ((congrArg (fun a : Γ(X, U) => X.presheaf.map (homOfLE hVU).op a) hs).trans (map_one _))

end MixedFujita
