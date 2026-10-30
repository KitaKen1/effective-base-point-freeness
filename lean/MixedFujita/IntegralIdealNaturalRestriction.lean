/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperIntegralNaturalRestriction
public import MixedFujita.NoetherianIdealCoherence
public import MixedFujita.AmpleIdealSubschemeRestrictionSerre

/-! 整閉部分への自然制限と全高次ample Serre延長。 See reports/check-256-natural-center-concentration-extension.json for the verified scope. On proper integral targets a nonzero endomorphism of a Cartier line is an isomorphism, using the actual global-functions field and TauCeti global scalar action. Any section-surjective morphism to a restricted Cartier pushforward therefore implies surjectivity of the NATURAL restriction. Every actual ideal module on a locally Noetherian source is coherent. High ample powers restrict naturally and surjectively to integral closed sources and actual lc centers by unconditional Serre vanishing. In the positive restricted original numerical-dimension branch, all large powers of one original nef-ample pencil have nonzero ambient sections with naturally restricted sections of arbitrarily high linear order at every smooth closed point. No center normality, KV or initial original L-section is assumed. Original mL center lifting, appropriate center adjoint vanishing/nonvanishing, nu=0, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Actual ideal-twist H1 vanishing gives surjectivity of the NATURAL restriction
of original Cartier sections to an integral closed source. -/
theorem integral_ideal_subscheme_natural_cartier_restriction_surjective_of_H1
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (I : X.IdealSheafData) [IsIntegral I.subscheme] (P : CartierDivisor X)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1)) :
    Function.Surjective (modulePullbackGlobalSections I.subschemeι P.sheaf) := by
  let : I.subscheme.Over (Spec (CommRingCat.of K)) := ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : I.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (I.subscheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := I.subschemeι)]
    infer_instance
  obtain ⟨r, hr⟩ := idealSheaf_cartier_restriction_exists_surjective_of_H1 P I hvan
  exact proper_integral_natural_cartier_restriction_surjective_of_surjective_map K I.subschemeι P r hr


/-- All sufficiently high ample twists restrict NATURALLY and surjectively to
ANY integral ideal subscheme. Coherence and properness are derived internally;
no usual KV, center normality or initial original L-section is assumed. -/
theorem integral_ideal_subscheme_all_high_ample_twists_natural_restriction
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) :
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      (∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology ((b • A).sheaf ⊗ idealSheafDataModule I) (q + 1))) ∧
      Function.Surjective (modulePullbackGlobalSections I.subschemeι (b • A).sheaf) := by
  let := locallyNoetherian_idealSheafDataModule_isCoherent I
  obtain ⟨b₀, hb⟩ := ample_ideal_subscheme_all_high_twists_serre_and_restriction A hA I
  refine ⟨b₀, ?_⟩
  intro b hbb
  have hv := (hb b hbb).1
  exact ⟨hv, integral_ideal_subscheme_natural_cartier_restriction_surjective_of_H1 K I (b • A) (hv 0)⟩

end MixedFujita
