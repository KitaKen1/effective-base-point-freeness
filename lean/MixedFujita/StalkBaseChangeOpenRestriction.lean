/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StalkBaseChangeVanishing
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion

/-! Transport actual stalk-base-change vanishing through a target open
restriction. The same local source is retained; the restricted pullback
square and the module comparison are constructed from the original square. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem stalk_baseChange_restrict_exists
    {T X Y : Scheme.{u}} {f : T ⟶ X} (U : X.Opens) (x : U)
    {g : Y ⟶ T} {g' : Y ⟶ Spec (X.presheaf.stalk x)}
    (H : IsPullback g g' f (X.fromSpecStalk x)) (M : T.Modules) :
    ∃ (a : Y ⟶ (f ⁻¹ᵁ U).toScheme)
      (b : Y ⟶ Spec (U.toScheme.presheaf.stalk x)),
      IsPullback a b (f ∣_ U) (U.toScheme.fromSpecStalk x) ∧
      Nonempty ((Scheme.Modules.pullback a).obj (M.restrict (f ⁻¹ᵁ U).ι) ≅
        (Scheme.Modules.pullback g).obj M) := by
  let σ := U.fromSpecStalkOfMem x x.property
  let R := (isPullback_morphismRestrict f U).flip
  have hw : g ≫ f = (g' ≫ σ) ≫ U.ι := by
    simpa only [σ, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι] using H.w
  let a := R.lift g (g' ≫ σ) hw
  have ha : a ≫ (f ⁻¹ᵁ U).ι = g := R.lift_fst _ _ _
  have hb : a ≫ (f ∣_ U) = g' ≫ σ := R.lift_snd _ _ _
  have H' : IsPullback a g' (f ∣_ U) σ := by
    apply IsPullback.of_right (t := R) (p := hb)
    simpa only [ha, σ, Scheme.Opens.fromSpecStalkOfMem_ι] using H
  let e := asIso (Spec.map (inv (U.ι.stalkMap x)))
  refine ⟨a, g' ≫ e.hom, H'.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [σ, e, Scheme.Opens.fromSpecStalkOfMem]), ?_⟩
  exact ⟨(Scheme.Modules.pullback a).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app M) ≪≫
    (Scheme.Modules.pullbackComp a (f ⁻¹ᵁ U).ι).app M ≪≫
    (Scheme.Modules.pullbackCongr ha).app M⟩

theorem all_stalk_baseChange_vanishing_restrict
    {T X : Scheme.{u}} (f : T ⟶ X) (M : T.Modules) (p : ℕ)
    (hlocal : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ T)
      (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' f (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1)))
    (U : X.Opens) (x : U) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ (f ⁻¹ᵁ U).toScheme)
      (b : Y ⟶ Spec (U.toScheme.presheaf.stalk x)),
      IsPullback a b (f ∣_ U) (U.toScheme.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H
        ((Scheme.Modules.pullback a).obj (M.restrict (f ⁻¹ᵁ U).ι)).toAbSheaf (p + 1)) := by
  obtain ⟨Y, g, g', H, hvan⟩ := hlocal x
  obtain ⟨a, b, H', ⟨e⟩⟩ := stalk_baseChange_restrict_exists U x H M
  let : Subsingleton ((Sheaf.functorH.{u} _ (p + 1)).obj
    ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pullback g).obj M))) := hvan
  refine ⟨Y, a, b, H', ?_⟩
  exact (((Sheaf.functorH.{u} _ (p + 1)).mapIso
    ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e))).addCommGroupIsoToAddEquiv.toEquiv.subsingleton

theorem affine_open_preimage_cohomology_vanish_of_all_stalk_baseChange
    {T X : Scheme.{u}} (f : T ⟶ X) [QuasiCompact f] [T.IsSeparated]
    (M : T.Modules) [M.IsQuasicoherent] (p : ℕ)
    (hlocal : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ T)
      (g' : Y ⟶ Spec (X.presheaf.stalk x)),
      IsPullback g g' f (X.fromSpecStalk x) ∧
      Subsingleton (Sheaf.H ((Scheme.Modules.pullback g).obj M).toAbSheaf (p + 1)))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Subsingleton (M.H' (p + 1) (f ⁻¹ᵁ U)) := by
  let : IsAffine U.toScheme := hU
  let : CompactSpace (f ⁻¹ᵁ U).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  let : (f ⁻¹ᵁ U).toScheme.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (f ⁻¹ᵁ U).ι]
    infer_instance⟩
  let := affine_target_cohomology_vanish_of_all_stalk_baseChange
    (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) p
    (all_stalk_baseChange_vanishing_restrict f M p hlocal U)
  have e := Scheme.Modules.cohomologyOnOpensRangeIso (f ⁻¹ᵁ U).ι M (p + 1)
  rw [Scheme.Opens.opensRange_ι] at e
  exact e.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end MixedFujita
