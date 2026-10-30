/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineBlowupReesBaseChange
public import Hironaka.Scheme.BlowUp.FlatBaseChange
public import Hironaka.Scheme.Smooth.BlowUpSmoothChart

/-! The explicit map of Rees blow-ups is the geometric flat base change.
This identifies the maps used in twisting-module transport with the maps in
the cartesian squares, including etale maps and arbitrary localizations. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type u} [CommRing R] [CommRing S]
  {I : Ideal R} {J : Ideal S} (φ : R →+* S) (hJ : I.map φ = J)

theorem affineBlowUp_mapOfEq_isPullback [Flat (Spec.map (CommRingCat.ofHom φ))] :
    IsPullback (affineBlowUp.mapOfEq φ hJ) (affineBlowUp.π J)
      (affineBlowUp.π I) (Spec.map (CommRingCat.ofHom φ)) := by
  have hB : IsBlowUp ((specIdealSheaf I).comap (Spec.map (CommRingCat.ofHom φ)))
      (affineBlowUp.π J) := by
    rw [specIdealSheaf_comap, hJ]
    exact affineBlowUp.isBlowUp J
  obtain ⟨f, hf⟩ := (affineBlowUp.isBlowUp I).exists_isPullback_of_flat _ hB
  have he : affineBlowUp.mapOfEq φ hJ = f := by
    apply (affineBlowUp.isBlowUp I).hom_ext
      (affineBlowUp.π J ≫ Spec.map (CommRingCat.ofHom φ)) _ _ _
      (affineBlowUp.mapOfEq_π φ hJ) hf.w
    rw [Scheme.IdealSheafData.comap_comp]
    exact hB.admissible
  exact he ▸ hf

theorem affineBlowUp_mapOfEq_isPullback_of_etale
    [Etale (Spec.map (CommRingCat.ofHom φ))] :
    IsPullback (affineBlowUp.mapOfEq φ hJ) (affineBlowUp.π J)
      (affineBlowUp.π I) (Spec.map (CommRingCat.ofHom φ)) :=
  affineBlowUp_mapOfEq_isPullback φ hJ

theorem affineBlowUp_mapOfEq_isPullback_of_flat (hφ : φ.Flat) :
    IsPullback (affineBlowUp.mapOfEq φ hJ) (affineBlowUp.π J)
      (affineBlowUp.π I) (Spec.map (CommRingCat.ofHom φ)) := by
  have : Flat (Spec.map (CommRingCat.ofHom φ)) := Flat.SpecMap_iff.mpr hφ
  exact affineBlowUp_mapOfEq_isPullback φ hJ

theorem affineBlowUp_localization_isPullback [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R) :
    IsPullback (affineBlowUp.mapOfEq (algebraMap R S) (I := I) rfl)
      (affineBlowUp.π (I.map (algebraMap R S))) (affineBlowUp.π I)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  exact affineBlowUp_mapOfEq_isPullback_of_flat _ rfl
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat S M))

end MixedFujita
