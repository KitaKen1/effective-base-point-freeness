/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothCentreLocalVanishing
public import MixedFujita.FiniteAffineCoverCohomology
public import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional

/-! Off the center, the actual stalk blow-up is affine: its defining ideal
is the unit ideal, and the universal property makes its projection an
isomorphism. Hence every Cartier sheaf on it has zero positive cohomology. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem isBlowUp_isIso_of_isInvertible {X B : Scheme.{u}}
    {I : X.IdealSheafData} {π : B ⟶ X} (hB : IsBlowUp I π)
    (hI : I.IsInvertible) : IsIso π := by
  have hid : (I.comap (𝟙 X)).IsInvertible := by
    rw [Scheme.IdealSheafData.comap_id]
    exact hI
  obtain ⟨s, hs⟩ := hB.exists_lift (𝟙 X) hid
  refine IsIso.mk' ⟨s, hs, ?_⟩
  exact hB.hom_ext π hB.admissible _ _
    (by rw [Category.assoc, hs, Category.comp_id]) (Category.id_comp _)

theorem localBlowUp_isIso_off_center {X : Scheme.{u}} (Z : X.IdealSheafData)
    (x : X) (hx : x ∉ Z.support) : IsIso (affineBlowUp.π (Z.stalkIdeal x)) := by
  apply isBlowUp_isIso_of_isInvertible (affineBlowUp.isBlowUp _)
  rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support Z hx,
    AlgebraicGeometry.Remark33.specIdealSheaf_top]
  exact Scheme.IdealSheafData.isInvertible_top

theorem localBlowUp_cartier_vanish_off_center {X : Scheme.{u}}
    [IsLocallyNoetherian X] (Z : X.IdealSheafData) (x : X) (hx : x ∉ Z.support)
    [IsIntegral (affineBlowUp (Z.stalkIdeal x))]
    (C : CartierDivisor (affineBlowUp (Z.stalkIdeal x))) (q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology C.sheaf (q + 1)) := by
  let := localBlowUp_isIso_off_center Z x hx
  let : IsAffine (affineBlowUp (Z.stalkIdeal x)) := IsAffine.of_isIso (affineBlowUp.π _)
  let : IsLocallyNoetherian (affineBlowUp (Z.stalkIdeal x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (affineBlowUp.π _)
  let := C.isInvertible_sheaf
  let := invertibleModule_isQuasicoherent C.sheaf
  let := finiteAffine_cohomologyOn_vanish C.sheaf (isAffineOpen_top _) (q + 1) (by omega)
  exact (Modules.cohomologyOnTopIso C.sheaf (q + 1)).symm.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end MixedFujita
