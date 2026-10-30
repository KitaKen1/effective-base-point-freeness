/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineLocalizationBaseChange
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-! The actual section maps of a localization base change, over one common
base ring. Restriction maps and the pullback unit are linear for these actions.
This removes the varying chart rings from finite Cech denominator descent. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def sectionBaseRingHom {A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) (U : X.Opens) : A →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom

@[instance_reducible]
def sectionBaseModule {A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) (M : X.Modules) (U : X.Opens) : Module A Γ(M, U) :=
  Module.compHom _ (sectionBaseRingHom f U)

theorem sectionBaseRingHom_restrict {A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) {U V : X.Opens} (h : U ≤ V) (r : A) :
    X.presheaf.map (homOfLE h).op (sectionBaseRingHom f V r) = sectionBaseRingHom f U r := by
  let : X.Over (Spec (.of A)) := ⟨f⟩
  have hn := ConcreteCategory.congr_hom
    ((X.baseRingToStructurePresheaf A).naturality (homOfLE h).op) r
  simp only [Scheme.baseRingToStructurePresheaf_app_eq_appLE] at hn
  exact hn.symm

theorem sectionBaseModule_restrict_smul {A : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec A) (M : X.Modules) :
    let : ∀ U : X.Opens, Module A Γ(M, U) := sectionBaseModule f M
    ∀ ⦃V W : X.Opens⦄ (h : W ≤ V) (r : A) (s : Γ(M, V)),
      M.presheaf.map (homOfLE h).op (r • s) = r • M.presheaf.map (homOfLE h).op s := by
  let : ∀ U : X.Opens, Module A Γ(M, U) := sectionBaseModule f M
  dsimp only
  intro V W h r s
  change M.presheaf.map (homOfLE h).op (sectionBaseRingHom f V r • s) =
    sectionBaseRingHom f W r • M.presheaf.map (homOfLE h).op s
  rw [Scheme.Modules.map_smul, sectionBaseRingHom_restrict]

def pullbackSectionPresheafMap {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) :
    M.presheaf ⟶ ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)).presheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf

theorem pullbackSectionPresheafMap_smul
    {A : CommRingCat.{u}} {X Y : Scheme.{u}} (f : X ⟶ Spec A) (g : Y ⟶ X) (M : X.Modules) :
    let : ∀ U : X.Opens, Module A Γ(M, U) := sectionBaseModule f M
    let : ∀ U : X.Opens, Module A
      Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M), U) :=
        sectionBaseModule f _
    ∀ (U : X.Opens) (r : A) (m : Γ(M, U)),
      (pullbackSectionPresheafMap g M).app (op U) (r • m) =
        r • (pullbackSectionPresheafMap g M).app (op U) m := by
  let : ∀ U : X.Opens, Module A Γ(M, U) := sectionBaseModule f M
  let : ∀ U : X.Opens, Module A
      Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M), U) :=
    sectionBaseModule f _
  dsimp only
  intro U r m
  exact (pullbackSectionLinearMap g M U).map_smul (sectionBaseRingHom f U r) m

def pullbackSectionBaseLinearMap {A : CommRingCat.{u}} {X Y : Scheme.{u}}
    (f : X ⟶ Spec A) (g : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    let := sectionBaseModule f M U
    let := sectionBaseModule f ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)) U
    Γ(M, U) →ₗ[A] Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M), U) :=
  let := sectionBaseModule f M U
  let := sectionBaseModule f ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)) U
  { toFun := Scheme.Modules.pullbackApp g M U
    map_add' := map_add _
    map_smul' := fun r m ↦ (pullbackSectionLinearMap g M U).map_smul (sectionBaseRingHom f U r) m }

theorem affine_localization_baseChange_baseModule
    {A L : CommRingCat.{u}} {β : A ⟶ L} {X Y : Scheme.{u}}
    {f : X ⟶ Spec A} {g : Y ⟶ X} {g' : Y ⟶ Spec L}
    (H : IsPullback g g' f (Spec.map β)) {U : X.Opens} (hU : IsAffineOpen U)
    (S : Submonoid A) (M : X.Modules) [M.IsQuasicoherent] :
    let := sectionBaseModule f M U
    let := sectionBaseModule f ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)) U
    let : Algebra A L := β.hom.toAlgebra
    IsLocalization S L → IsLocalizedModule S (pullbackSectionBaseLinearMap f g M U) := by
  let := sectionBaseModule f M U
  let := sectionBaseModule f ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)) U
  let : Algebra A L := β.hom.toAlgebra
  dsimp only
  intro hloc
  let : Algebra A Γ(X, U) := (sectionBaseRingHom f U).toAlgebra
  let : IsScalarTower A Γ(X, U) Γ(M, U) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower A Γ(X, U)
      Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M), U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid Γ(X, U) S)
      (pullbackSectionLinearMap g M U) := affine_localization_baseChange_module H hU S M hloc
  exact IsLocalizedModule.restrictScalars S (pullbackSectionLinearMap g M U)

end
end MixedFujita
