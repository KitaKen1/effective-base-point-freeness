/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffinePullbackSectionLocalization
public import Mathlib.Algebra.Category.Ring.Constructions

/-! A Cartesian base change by a ring localization gives localization on
every affine source chart. Applied to the actual pullback map of a
quasi-coherent module, this constructs denominators and detects its kernel. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem commRing_pushout_isLocalization
    {A B L C : CommRingCat.{u}} (α : A ⟶ B) (β : A ⟶ L) (γ : B ⟶ C) (δ : L ⟶ C)
    (H : IsPushout α β γ δ) (S : Submonoid A) :
    let : Algebra A L := β.hom.toAlgebra
    let : Algebra B C := γ.hom.toAlgebra
    IsLocalization S L → IsLocalization (S.map α.hom) C := by
  let : Algebra A L := β.hom.toAlgebra
  let : Algebra B C := γ.hom.toAlgebra
  dsimp only
  intro hloc
  let := hloc
  let : Algebra A B := α.hom.toAlgebra
  let : Algebra L C := δ.hom.toAlgebra
  let : Algebra A C := (α ≫ γ).hom.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A L C := IsScalarTower.of_algebraMap_eq fun a ↦
    ConcreteCategory.congr_hom H.w a
  have h : Algebra.IsPushout A B L C := CommRingCat.isPushout_iff_isPushout.mp H
  exact (Algebra.isLocalization_iff_isPushout S L).mpr h

variable {A L : CommRingCat.{u}} {β : A ⟶ L} {X Y : Scheme.{u}}
  {f : X ⟶ Spec A} {g : Y ⟶ X} {g' : Y ⟶ Spec L}
  (H : IsPullback g g' f (Spec.map β)) {U : X.Opens} (hU : IsAffineOpen U)
  (S : Submonoid A)

include H hU

theorem affine_localization_baseChange_ring :
    let : Algebra A L := β.hom.toAlgebra
    let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    IsLocalization S L →
      IsLocalization (S.map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom)
        Γ(Y, g ⁻¹ᵁ U) :=
  commRing_pushout_isLocalization _ _ _ _ (CohomologyAux.isPushout_baseChange H hU) S

theorem affine_localization_baseChange_section_exists_denominator
    (M : X.Modules) [M.IsQuasicoherent] :
    let : Algebra A L := β.hom.toAlgebra
    IsLocalization S L →
    ∀ z : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U),
      ∃ (s : S) (m : Γ(M, U)),
        g.app U (((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) s) • z =
          Scheme.Modules.pullbackApp g M U m := by
  let : Algebra A L := β.hom.toAlgebra
  dsimp only
  intro hloc z
  let : IsAffineHom g := CohomologyAux.isAffineHom_of_isPullback H
  obtain ⟨s, m, hm⟩ := affine_pullback_section_exists_denominator g M hU (hU.preimage g)
    _ (affine_localization_baseChange_ring H hU S hloc) z
  obtain ⟨a, ha, he⟩ := s.property
  refine ⟨⟨a, ha⟩, m, ?_⟩
  simpa only [← he] using hm

theorem affine_localization_baseChange_section_eq_zero_iff
    (M : X.Modules) [M.IsQuasicoherent] :
    let : Algebra A L := β.hom.toAlgebra
    IsLocalization S L →
    ∀ m : Γ(M, U), Scheme.Modules.pullbackApp g M U m = 0 ↔
      ∃ s : S, (((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) s) • m = 0 := by
  let : Algebra A L := β.hom.toAlgebra
  dsimp only
  intro hloc m
  let : IsAffineHom g := CohomologyAux.isAffineHom_of_isPullback H
  rw [affine_pullback_section_eq_zero_iff g M hU (hU.preimage g) _
    (affine_localization_baseChange_ring H hU S hloc)]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha, he⟩ := s.property
    exact ⟨⟨a, ha⟩, by simpa only [← he] using hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨_, ⟨s, s.property, rfl⟩⟩, hs⟩

theorem affine_localization_baseChange_module
    (M : X.Modules) [M.IsQuasicoherent] :
    let : Algebra A L := β.hom.toAlgebra
    IsLocalization S L →
      IsLocalizedModule (S.map ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom)
        (pullbackSectionLinearMap g M U) := by
  let : Algebra A L := β.hom.toAlgebra
  dsimp only
  intro hloc
  let : IsAffineHom g := CohomologyAux.isAffineHom_of_isPullback H
  exact affine_pullback_section_isLocalizedModule g M hU (hU.preimage g) _
    (affine_localization_baseChange_ring H hU S hloc)

end MixedFujita
