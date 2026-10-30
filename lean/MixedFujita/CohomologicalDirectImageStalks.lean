/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteAffineCoverCohomology
public import Mathlib.Topology.Sheaves.Sheafify

/-! The sheaf associated to U ↦ H^q(f⁻¹ U,M), using the existing actual
cohomology groups and restriction maps. We prove stalk vanishing from a
cofinal family of acyclic neighbourhoods. No derived-functor comparison or
coherence of this associated sheaf is assumed or asserted here. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open TopCat.Presheaf
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem additivePresheaf_stalk_subsingleton_of_cofinal_vanishing
    {X : TopCat.{u}} (F : X.Presheaf AddCommGrpCat.{u}) (x : X)
    (h : ∀ U : Opens X, x ∈ U → ∃ V : Opens X,
      x ∈ V ∧ V ≤ U ∧ Subsingleton (F.obj (op V))) :
    Subsingleton (F.stalk x) := by
  apply subsingleton_of_forall_eq 0
  intro s
  obtain ⟨U, hxU, a, rfl⟩ := F.exists_germ_eq s
  obtain ⟨V, hxV, hVU, hV⟩ := h U hxU
  letI := hV
  rw [← F.germ_res_apply (homOfLE hVU) x hxV a]
  rw [Subsingleton.elim (F.map (homOfLE hVU).op a) 0, map_zero]

theorem associatedSheaf_stalk_subsingleton_of_presheaf
    {X : TopCat.{u}} (F : X.Presheaf AddCommGrpCat.{u}) (x : X)
    (h : Subsingleton (F.stalk x)) :
    Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj F).obj x) := by
  letI : Subsingleton ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F) := h
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat F
  exact (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (toSheafify (Opens.grothendieckTopology X) F))).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- The actual inverse-image-open cohomology presheaf. -/
noncomputable def cohomologicalDirectImagePresheaf
    {T X : Scheme.{u}} (f : T ⟶ X) (M : T.Modules) (q : ℕ) :
    TopCat.Presheaf AddCommGrpCat.{u} X :=
  f.base _* (CategoryTheory.Sheaf.cohomologyPresheaf.{u}
    ((_root_.SheafOfModules.toSheaf T.ringCatSheaf).obj M) q)

/-- The associated abelian sheaf of inverse-image-open cohomology. -/
noncomputable def cohomologicalDirectImage
    {T X : Scheme.{u}} (f : T ⟶ X) (M : T.Modules) (q : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (cohomologicalDirectImagePresheaf f M q)

theorem cohomologicalDirectImagePresheaf_obj
    {T X : Scheme.{u}} (f : T ⟶ X) (M : T.Modules) (q : ℕ) (U : X.Opens) :
    (cohomologicalDirectImagePresheaf f M q).obj (op U) =
      Modules.cohomologyOn M q (f ⁻¹ᵁ U) := rfl

theorem cohomologicalDirectImage_stalk_subsingleton_of_cofinal_vanishing
    {T X : Scheme.{u}} (f : T ⟶ X) (M : T.Modules) (q : ℕ) (x : X)
    (h : ∀ U : X.Opens, x ∈ U → ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧
      Subsingleton (Modules.cohomologyOn M q (f ⁻¹ᵁ V))) :
    Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (cohomologicalDirectImage f M q).obj x) := by
  apply associatedSheaf_stalk_subsingleton_of_presheaf
  exact additivePresheaf_stalk_subsingleton_of_cofinal_vanishing
    (cohomologicalDirectImagePresheaf f M q) x h

end MixedFujita
