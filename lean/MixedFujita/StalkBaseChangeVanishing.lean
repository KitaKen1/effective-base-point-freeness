/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CohomologyLocalizationAnnihilator
public import Mathlib.RingTheory.Ideal.Maximal

/-! On an affine base, vanishing after every actual stalk base change
implies vanishing on the whole quasi-compact source with affine diagonal.
Each class has an annihilator outside every prime, so its annihilator ideal
is the unit ideal. This avoids constructing a higher-direct-image comparison. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem module_eq_zero_of_primewise_annihilators
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : M)
    (h : ∀ p : PrimeSpectrum R, ∃ s : R, s ∉ p.asIdeal ∧ s • a = 0) : a = 0 := by
  by_contra ha
  let I := (Submodule.span R ({a} : Set M)).annihilator
  have hI : I ≠ ⊤ := by
    intro he
    have h1 : (1 : R) ∈ I := by rw [he]; exact Submodule.mem_top
    exact ha (by simpa only [one_smul] using
      (Submodule.mem_annihilator_span_singleton a 1).mp h1)
  obtain ⟨J, hJ, hIJ⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsa⟩ := h ⟨J, hJ.isPrime⟩
  exact hs (hIJ ((Submodule.mem_annihilator_span_singleton a s).mpr hsa))

theorem cohomology_vanish_of_all_stalk_baseChange
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (p : ℕ)
    (hlocal : ∀ x : Spec A, ∃ (Y : Scheme.{u}) (g : Y ⟶ X)
      (g' : Y ⟶ Spec ((Spec A).presheaf.stalk x)),
      IsPullback g g' f ((Spec A).fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1))) :
    Subsingleton (Sheaf.H M.toAbSheaf (p + 1)) := by
  let : Module A (M.H (p + 1)) := Module.compHom _ (sectionBaseRingHom f ⊤)
  have hH : Subsingleton (M.H (p + 1)) := by
    apply subsingleton_of_forall_eq 0
    intro a
    apply module_eq_zero_of_primewise_annihilators (R := A) a
    intro x
    obtain ⟨Y, g, g', H, hvan⟩ := hlocal x
    exact stalk_baseChange_cohomology_annihilator x H M p hvan a
  let := hH
  exact (Scheme.Modules.H.addEquivSheafH M (p + 1)).symm.toEquiv.subsingleton

theorem affine_target_cohomology_vanish_of_all_stalk_baseChange
    {T X : Scheme.{u}} [IsAffine X] (f : T ⟶ X)
    (M : T.Modules) [M.IsQuasicoherent]
    [CompactSpace T] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from T))]
    (p : ℕ)
    (hlocal : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ T)
      (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' f (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1))) :
    Subsingleton (Sheaf.H M.toAbSheaf (p + 1)) := by
  let F := f ≫ X.toSpecΓ
  let : Module Γ(X, ⊤) (M.H (p + 1)) := Module.compHom _ (sectionBaseRingHom F ⊤)
  have hH : Subsingleton (M.H (p + 1)) := by
    apply subsingleton_of_forall_eq 0
    intro a
    apply module_eq_zero_of_primewise_annihilators (R := Γ(X, ⊤)) a
    intro z
    let x := (isAffineOpen_top X).fromSpec z
    obtain ⟨Y, g, g', H, hvan⟩ := hlocal x
    have H' : IsPullback g g' F (Spec.map (X.presheaf.germ ⊤ x trivial)) :=
      H.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso X.toSpecΓ)
        (by simp) (by simp) (by simp [F]) (by simp [Scheme.fromSpecStalk_toSpecΓ])
    obtain ⟨s, hs⟩ := localization_baseChange_cohomology_annihilator H' z.asIdeal.primeCompl M p
      hvan ((isAffineOpen_top X).isLocalization_stalk' z trivial) a
    exact ⟨s, s.property, hs⟩
  let := hH
  exact (Scheme.Modules.H.addEquivSheafH M (p + 1)).symm.toEquiv.subsingleton

end MixedFujita
