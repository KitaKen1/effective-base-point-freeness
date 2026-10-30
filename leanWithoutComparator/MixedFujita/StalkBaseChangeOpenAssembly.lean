/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StalkBaseChangeRelativeVanishing

/-! Paste a stalk square on an open neighborhood into the original square.
Different points may use different opens and local models. Module pullback
composition gives an actual local-to-global vanishing assembly. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem stalk_baseChange_paste_open
    {T X B Y : Scheme.{u}} {f : T ⟶ X} (U : X.Opens) (x : U)
    {a : B ⟶ T} {b : B ⟶ U.toScheme} (H : IsPullback a b f U.ι)
    {g : Y ⟶ B} {g' : Y ⟶ Spec (U.toScheme.presheaf.stalk x)}
    (H' : IsPullback g g' b (U.toScheme.fromSpecStalk x)) :
    ∃ s : Y ⟶ Spec (X.presheaf.stalk x),
      IsPullback (g ≫ a) s f (X.fromSpecStalk x) := by
  let e := asIso (Spec.map (inv (U.ι.stalkMap x)))
  have he : e.inv ≫ X.fromSpecStalk x = U.toScheme.fromSpecStalk x ≫ U.ι := by
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι U x x.property]
    simp [Scheme.Opens.fromSpecStalkOfMem, e]
  exact ⟨g' ≫ e.inv, (H'.paste_horiz H).of_iso
    (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
    (by simp) (by simp) (by simp) (by simpa using he.symm)⟩

theorem stalk_baseChange_vanishing_paste_open
    {T X B Y : Scheme.{u}} {f : T ⟶ X} (U : X.Opens) (x : U)
    {a : B ⟶ T} {b : B ⟶ U.toScheme} (H : IsPullback a b f U.ι)
    {g : Y ⟶ B} {g' : Y ⟶ Spec (U.toScheme.presheaf.stalk x)}
    (H' : IsPullback g g' b (U.toScheme.fromSpecStalk x))
    (M : T.Modules) (p : ℕ)
    (hvan : Subsingleton (Sheaf.H
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M)).toAbSheaf (p + 1))) :
    ∃ s : Y ⟶ Spec (X.presheaf.stalk x),
      IsPullback (g ≫ a) s f (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback (g ≫ a)).obj M).toAbSheaf (p + 1)) := by
  obtain ⟨s, hs⟩ := stalk_baseChange_paste_open U x H H'
  let e := (Scheme.Modules.pullbackComp g a).app M
  let : Subsingleton ((Sheaf.functorH.{u} _ (p + 1)).obj
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      ((Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback g).obj M))) := hvan
  exact ⟨s, hs, (((Sheaf.functorH.{u} _ (p + 1)).mapIso
    ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e)).symm).addCommGroupIsoToAddEquiv.toEquiv.subsingleton⟩

theorem relative_vanishing_of_open_local_stalk_baseChanges
    {T X : Scheme.{u}} (f : T ⟶ X) [QuasiCompact f] [T.IsSeparated]
    (M : T.Modules) [M.IsQuasicoherent] (p : ℕ)
    (hlocal : ∀ x : X, ∃ (U : X.Opens) (hx : x ∈ U)
      (B : Scheme.{u}) (a : B ⟶ T) (b : B ⟶ U.toScheme),
      IsPullback a b f U.ι ∧
      ∃ (Y : Scheme.{u}) (g : Y ⟶ B)
        (g' : Y ⟶ Spec (U.toScheme.presheaf.stalk ⟨x, hx⟩)),
        IsPullback g g' b (U.toScheme.fromSpecStalk ⟨x, hx⟩) ∧
        Subsingleton (Sheaf.H
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M)).toAbSheaf (p + 1))) :
    (∀ U : X.Opens, IsAffineOpen U → Subsingleton (M.H' (p + 1) (f ⁻¹ᵁ U))) ∧
    Limits.IsZero (cohomologicalDirectImage f M (p + 1)) := by
  have h : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ T)
      (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' f (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1)) := by
    intro x
    obtain ⟨U, hx, B, a, b, H, Y, g, g', H', hv⟩ := hlocal x
    obtain ⟨s, hs, hvan⟩ := stalk_baseChange_vanishing_paste_open U ⟨x, hx⟩ H H' M p hv
    exact ⟨Y, g ≫ a, s, hs, hvan⟩
  exact ⟨fun _ hU ↦ affine_open_preimage_cohomology_vanish_of_all_stalk_baseChange f M p h hU,
    cohomologicalDirectImage_isZero_of_all_stalk_baseChange f M p h⟩

end MixedFujita
