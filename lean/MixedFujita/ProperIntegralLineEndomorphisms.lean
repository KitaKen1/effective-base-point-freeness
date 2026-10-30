/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierTwistExactness
public import MixedFujita.CartierGlobalPullback
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! 固有整源の非零可逆層自己準同型の同型性。 See reports/check-256-natural-center-concentration-extension.json for the verified scope. On proper integral targets a nonzero endomorphism of a Cartier line is an isomorphism, using the actual global-functions field and TauCeti global scalar action. Any section-surjective morphism to a restricted Cartier pushforward therefore implies surjectivity of the NATURAL restriction. Every actual ideal module on a locally Noetherian source is coherent. High ample powers restrict naturally and surjectively to integral closed sources and actual lc centers by unconditional Serre vanishing. In the positive restricted original numerical-dimension branch, all large powers of one original nef-ample pencil have nonzero ambient sections with naturally restricted sections of arbitrarily high linear order at every smooth closed point. No center normality, KV or initial original L-section is assumed. Original mL center lifting, appropriate center adjoint vanishing/nonvanishing, nu=0, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower


/-- Every nonzero structure-sheaf endomorphism on an integral universally closed
scheme over a field is an isomorphism. The global-functions field is internal. -/
theorem proper_integral_unit_endomorphism_isIso_of_ne_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [UniversallyClosed (X ↘ Spec (CommRingCat.of K))]
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hf : f ≠ 0) : IsIso f := by
  let a : Γ(X, ⊤) := Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤))
  have hscalar : f = Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) a := by
    apply (SheafOfModules.unitHomEquiv (SheafOfModules.unit X.ringCatSheaf)).injective
    apply PresheafOfModules.sections_ext
    intro U
    simp only [SheafOfModules.unitHomEquiv_apply_coe]
    let : CommRing (X.ringCatSheaf.obj.obj U) := inferInstanceAs (CommRing (X.presheaf.obj U))
    have hn := PresheafOfModules.naturality_apply f.val U.unop.leTop.op (1 : Γ(X, ⊤))
    change (f.val.app U).hom (X.presheaf.map U.unop.leTop.op (1 : Γ(X, ⊤))) =
      X.presheaf.map U.unop.leTop.op a at hn
    let r : X.ringCatSheaf.obj.obj U := X.presheaf.map U.unop.leTop.op a
    change Scheme.Modules.Hom.app f U.unop (1 : X.ringCatSheaf.obj.obj U) =
      Scheme.Modules.Hom.app (Scheme.Modules.globalSectionsSmul (SheafOfModules.unit X.ringCatSheaf) a) U.unop
        (1 : X.ringCatSheaf.obj.obj U)
    rw [Scheme.Modules.globalSectionsSmul_app]
    change (f.val.app U).hom (1 : X.ringCatSheaf.obj.obj U) = r * 1
    simpa only [map_one, mul_one] using hn
  have ha : a ≠ 0 := by
    intro h
    apply hf
    rw [hscalar, h, Scheme.Modules.globalSectionsSmul_zero]
  have haunit : IsUnit a := by
    let := (isField_of_universallyClosed K (X ↘ Spec (CommRingCat.of K))).toField
    exact isUnit_iff_ne_zero.mpr ha
  obtain ⟨v, hv⟩ := haunit
  rw [hscalar, ← hv]
  exact Scheme.Modules.isIso_globalSectionsSmul_units _ v


/-- Tensor cancellation transfers the global-functions field argument to an
actual Cartier sheaf on a proper integral source. No normality is required. -/
theorem proper_integral_cartier_endomorphism_isIso_of_ne_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [UniversallyClosed (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (f : D.sheaf ⟶ D.sheaf) (hf : f ≠ 0) : IsIso f := by
  let F := cartierTwistFunctor (-D)
  let e : F.obj D.sheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
    cartierTensorSheafIso (-D) D ≪≫ eqToIso (congrArg CartierDivisor.sheaf (neg_add_cancel D)) ≪≫
      cartierZeroSheafIso X
  let g := e.inv ≫ F.map f ≫ e.hom
  have hg : g ≠ 0 := by
    intro h
    have hzero : F.map f = 0 := by
      have h' := congrArg (fun q => e.hom ≫ q ≫ e.inv) h
      simpa only [g, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id,
        comp_zero, zero_comp] using h'
    apply hf
    apply F.map_injective
    simpa only [Functor.map_zero] using hzero
  let : IsIso g := proper_integral_unit_endomorphism_isIso_of_ne_zero K g hg
  have hfac : F.map f = e.hom ≫ g ≫ e.inv := by simp [g]
  let : IsIso (F.map f) := by rw [hfac]; infer_instance
  exact isIso_of_reflects_iso f F


/-- Every nonzero endomorphism of an actual restricted Cartier line is an
isomorphism when the target is integral and proper over the field. -/
theorem proper_integral_restricted_cartier_endomorphism_isIso_of_ne_zero
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [UniversallyClosed (Y ↘ Spec (CommRingCat.of K))]
    (i : Y ⟶ X) (P : CartierDivisor X)
    (f : (Scheme.Modules.pullback i).obj P.sheaf ⟶ (Scheme.Modules.pullback i).obj P.sheaf)
    (hf : f ≠ 0) : IsIso f := by
  obtain ⟨E, ⟨e⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor P i
  let g := e.inv ≫ f ≫ e.hom
  have hg : g ≠ 0 := by
    intro h
    apply hf
    have h' := congrArg (fun q => e.hom ≫ q ≫ e.inv) h
    simpa only [g, Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id,
      comp_zero, zero_comp] using h'
  let : IsIso g := proper_integral_cartier_endomorphism_isIso_of_ne_zero K E g hg
  have hfac : f = e.hom ≫ g ≫ e.inv := by simp [g]
  rw [hfac]
  infer_instance

end MixedFujita
