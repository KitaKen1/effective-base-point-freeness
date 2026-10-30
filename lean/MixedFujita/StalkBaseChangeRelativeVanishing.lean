/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StalkBaseChangeOpenRestriction
public import MixedFujita.CohomologicalDirectImageStalks
public import Mathlib.Topology.Sheaves.Abelian

/-! Actual stalk-base-change vanishing implies vanishing on affine inverse
images and of the associated cohomology sheaf. This uses an affine basis
and sheafification, without a derived-functor comparison. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem cohomologicalDirectImage_stalk_subsingleton_of_affine_vanishing
    {T X : Scheme.{u}} (f : T ⟶ X) (M : T.Modules) (q : ℕ)
    (h : ∀ U : X.Opens, IsAffineOpen U → Subsingleton (M.H' q (f ⁻¹ᵁ U))) (x : X) :
    Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (cohomologicalDirectImage f M q).obj x) := by
  apply cohomologicalDirectImage_stalk_subsingleton_of_cofinal_vanishing
  intro U hxU
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
  exact ⟨V, hxV, hVU, h V hV⟩

theorem cohomologicalDirectImage_isZero_of_affine_vanishing
    {T X : Scheme.{u}} (f : T ⟶ X) (M : T.Modules) (q : ℕ)
    (h : ∀ U : X.Opens, IsAffineOpen U → Subsingleton (M.H' q (f ⁻¹ᵁ U))) :
    Limits.IsZero (cohomologicalDirectImage f M q) := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
  intro x
  change Limits.IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    (cohomologicalDirectImage f M q).obj x)
  let : Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
    (cohomologicalDirectImage f M q).obj x) :=
    cohomologicalDirectImage_stalk_subsingleton_of_affine_vanishing f M q h x
  exact AddCommGrpCat.isZero_of_subsingleton _

theorem cohomologicalDirectImage_isZero_of_all_stalk_baseChange
    {T X : Scheme.{u}} (f : T ⟶ X) [QuasiCompact f] [T.IsSeparated]
    (M : T.Modules) [M.IsQuasicoherent] (p : ℕ)
    (hlocal : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ T)
      (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' f (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1))) :
    Limits.IsZero (cohomologicalDirectImage f M (p + 1)) := by
  apply cohomologicalDirectImage_isZero_of_affine_vanishing
  intro U hU
  exact affine_open_preimage_cohomology_vanish_of_all_stalk_baseChange f M p hlocal hU

end MixedFujita
