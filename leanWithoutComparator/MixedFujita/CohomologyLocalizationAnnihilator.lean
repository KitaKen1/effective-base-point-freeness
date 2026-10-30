/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartesianLocalizationCechDescent
public import Mathlib.AlgebraicGeometry.Stalk

/-! A common denominator for a Cech cocycle annihilates its actual sheaf
cohomology class, by the linear Leray comparison. Applied to the actual
base change to Spec of a stalk, the denominator avoids the corresponding
prime. No cohomology base-change isomorphism is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TopCat.Presheaf HomologicalComplex
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem homology_annihilator_of_cocycle_boundaries
    {R : Type*} [CommRing R] (S : Submonoid R)
    (K : CochainComplex AddCommGrpCat.{u} ℕ) (p : ℕ) (ρ : R → (K ⟶ K))
    (hboundary : ∀ c : K.X (p + 1), K.d (p + 1) (p + 2) c = 0 →
      ∃ (s : S) (b : K.X p), K.d p (p + 1) b = (ρ s).f (p + 1) c)
    (a : K.homology (p + 1)) :
    ∃ s : S, homologyMap (ρ s) (p + 1) a = 0 := by
  have hπ : Function.Surjective (K.homologyπ (p + 1)) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨v, rfl⟩ := hπ a
  have hv : K.d (p + 1) (p + 2) (K.iCycles (p + 1) v) = 0 := by
    rw [← ConcreteCategory.comp_apply, K.iCycles_d]
    rfl
  obtain ⟨s, b, hb⟩ := hboundary _ hv
  have he : cyclesMap (ρ s) (p + 1) v = K.toCycles p (p + 1) b := by
    apply (AddCommGrpCat.mono_iff_injective (K.iCycles (p + 1))).mp inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply,
      ← hb, ← ConcreteCategory.comp_apply, K.toCycles_i]
  refine ⟨s, ?_⟩
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality, ConcreteCategory.comp_apply,
    he, ← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ]
  rfl

theorem localization_baseChange_cohomology_annihilator
    {A L : CommRingCat.{u}} {β : A ⟶ L} {X Y : Scheme.{u}}
    {f : X ⟶ Spec A} {g : Y ⟶ X} {g' : Y ⟶ Spec L}
    (H : IsPullback g g' f (Spec.map β)) (S : Submonoid A)
    (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (p : ℕ)
    (hvan : Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1))) :
    let : Algebra A L := β.hom.toAlgebra
    IsLocalization S L → ∀ a : M.H (p + 1),
      ∃ s : S, sectionBaseRingHom f ⊤ s • a = 0 := by
  let : Algebra A L := β.hom.toAlgebra
  dsimp only
  intro hloc a
  obtain ⟨n, U, hcover, hU⟩ := CohomologyAux.exists_cechCover X
  let e : (cechComplex U M.presheaf).homology (p + 1) ≃ₗ[Γ(X, ⊤)] M.H (p + 1) :=
    (M.cechHomologyLinearEquiv U (p + 1) hU).trans
      (CohomologyAux.H'CongrOpens M (p + 1) hcover)
  let K := cechComplex U M.presheaf
  let ρ : A → (K ⟶ K) := fun s ↦ cechComplexMap U (M.smulHom (sectionBaseRingHom f ⊤ s)).hom
  have hboundary : ∀ c : K.X (p + 1), K.d (p + 1) (p + 2) c = 0 →
      ∃ (s : S) (b : K.X p), K.d p (p + 1) b = (ρ s).f (p + 1) c := by
    intro c hc
    obtain ⟨s, b, hb⟩ := localization_baseChange_cech_denominator_of_cohomology_vanishing
      H S M U hU hcover p hvan hloc c ((cechComplex_d_apply U M.presheaf (p + 1) c).symm.trans hc)
    refine ⟨s, b, ?_⟩
    rw [cechComplex_d_apply]
    change cechD U M.presheaf p b =
      cechCochainMap U (M.smulHom (sectionBaseRingHom f ⊤ s)).hom (p + 1) c
    funext i
    change cechD U M.presheaf p b i =
      X.presheaf.map (homOfLE (le_top : cechOpen U i ≤ ⊤)).op
        (sectionBaseRingHom f ⊤ s) • c i
    rw [sectionBaseRingHom_restrict]
    exact hb i
  obtain ⟨s, hs⟩ := homology_annihilator_of_cocycle_boundaries S K p ρ hboundary (e.symm a)
  refine ⟨s, ?_⟩
  have hs' : sectionBaseRingHom f ⊤ s • e.symm a = 0 := hs
  have he := congrArg e hs'
  simpa only [map_smul, LinearEquiv.apply_symm_apply, map_zero] using he

theorem stalk_baseChange_cohomology_annihilator
    {A : CommRingCat.{u}} {X Y : Scheme.{u}} {f : X ⟶ Spec A}
    (x : Spec A) {g : Y ⟶ X} {g' : Y ⟶ Spec ((Spec A).presheaf.stalk x)}
    (H : IsPullback g g' f ((Spec A).fromSpecStalk x))
    (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (p : ℕ)
    (hvan : Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1)))
    (a : M.H (p + 1)) :
    ∃ s : A, s ∉ x.asIdeal ∧ sectionBaseRingHom f ⊤ s • a = 0 := by
  rw [Spec.fromSpecStalk_eq'] at H
  obtain ⟨s, hs⟩ := localization_baseChange_cohomology_annihilator H x.asIdeal.primeCompl M p
    hvan (StructureSheaf.IsLocalization.to_stalk A x) a
  exact ⟨s, s.property, hs⟩

end MixedFujita
