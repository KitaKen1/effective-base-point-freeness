/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperIntegralSmoothComponent
public import MixedFujita.ClosedEmbeddingSheafExactness
public import MixedFujita.ConnectedRegularCentre
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! A regular Noetherian center can be isolated component by component in
ambient open neighborhoods. The restricted ideal defines the actual open
subscheme of the center, via a constructed scheme isomorphism. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable def centreOpenRestrictionIso
    {X : Scheme.{u}} (Z : X.IdealSheafData) (U : X.Opens) :
    (Z.comap U.ι).subscheme ≅ (Z.subschemeι ⁻¹ᵁ U).toScheme :=
  Z.comapIso U.ι ≪≫ (isPullback_morphismRestrict Z.subschemeι U).isoPullback.symm

@[reassoc (attr := simp)]
theorem centreOpenRestrictionIso_hom_inclusion
    {X : Scheme.{u}} (Z : X.IdealSheafData) (U : X.Opens) :
    (centreOpenRestrictionIso Z U).hom ≫ (Z.subschemeι ∣_ U) =
      (Z.comap U.ι).subschemeι := by
  simp [centreOpenRestrictionIso]

theorem regularCentre_exists_integral_open_restriction
    {X : Scheme.{u}} (Z : X.IdealSheafData)
    [IsNoetherian Z.subscheme] [IsRegular Z.subscheme]
    (x : X) (hx : x ∈ Z.support) :
    ∃ U : X.Opens, x ∈ U ∧ IsIntegral (Z.comap U.ι).subscheme ∧
      IsClosed ((Z.subschemeι ⁻¹ᵁ U : Z.subscheme.Opens) : Set Z.subscheme) := by
  obtain ⟨z, rfl⟩ := Z.exists_subschemeι_eq hx
  obtain ⟨V, hzV, hclosed, hV, _⟩ := regularScheme_exists_clopen_integral_component z
  obtain ⟨U, _, hU⟩ := inducing_relative_open_lift Z.subschemeι.isClosedEmbedding.isInducing
    (⊤ : X.Opens) V (by intro y hy; trivial)
  have hpre : Z.subschemeι ⁻¹ᵁ U = V := hU
  let : IsIntegral (Z.subschemeι ⁻¹ᵁ U).toScheme := by rw [hpre]; exact hV
  refine ⟨U, ?_, IsIntegral.of_isIso (centreOpenRestrictionIso Z U).inv, ?_⟩
  · change z ∈ Z.subschemeι ⁻¹ᵁ U
    rwa [hpre]
  · rwa [hpre]

theorem sncCentre_exists_integral_open_restriction
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] (x : X) (hx : x ∈ Z.support) :
    ∃ U : X.Opens, x ∈ U ∧ IsIntegral (Z.comap U.ι).subscheme ∧
      IsClosed ((Z.subschemeι ⁻¹ᵁ U : Z.subscheme.Opens) : Set Z.subscheme) := by
  let : IsRegular Z.subscheme := HasSncWith.isRegular f hZ
  exact regularCentre_exists_integral_open_restriction Z x hx

end MixedFujita
