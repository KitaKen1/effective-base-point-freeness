/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperIntegralLineEndomorphisms

/-! 固有整源の随伴自己準同型から自然制限Γ全射。 See reports/check-256-natural-center-concentration-extension.json for the verified scope. On proper integral targets a nonzero endomorphism of a Cartier line is an isomorphism, using the actual global-functions field and TauCeti global scalar action. Any section-surjective morphism to a restricted Cartier pushforward therefore implies surjectivity of the NATURAL restriction. Every actual ideal module on a locally Noetherian source is coherent. High ample powers restrict naturally and surjectively to integral closed sources and actual lc centers by unconditional Serre vanishing. In the positive restricted original numerical-dimension branch, all large powers of one original nef-ample pencil have nonzero ambient sections with naturally restricted sections of arbitrarily high linear order at every smooth closed point. No center normality, KV or initial original L-section is assumed. Original mL center lifting, appropriate center adjoint vanishing/nonvanishing, nu=0, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- On an integral proper target, any section-surjective map into the actual
pushforward of the restricted Cartier line forces the NATURAL restriction map
to be section-surjective. The adjunct is zero or an invertible endomorphism. -/
theorem proper_integral_natural_cartier_restriction_surjective_of_surjective_map
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [UniversallyClosed (Y ↘ Spec (CommRingCat.of K))]
    (i : Y ⟶ X) (P : CartierDivisor X)
    (r : P.sheaf ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj P.sheaf))
    (hr : Function.Surjective (Scheme.Modules.Hom.app r ⊤)) :
    Function.Surjective (modulePullbackGlobalSections i P.sheaf) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction i
  let f := (a.homEquiv P.sheaf ((Scheme.Modules.pullback i).obj P.sheaf)).symm r
  have hfac : a.unit.app P.sheaf ≫ (Scheme.Modules.pushforward i).map f = r := by
    exact (a.homEquiv P.sheaf ((Scheme.Modules.pullback i).obj P.sheaf)).apply_symm_apply r
  have hη : Function.Surjective (Scheme.Modules.Hom.app (a.unit.app P.sheaf) ⊤) := by
    by_cases hf : f = 0
    · have hrzero : r = 0 := by rw [← hfac, hf, Functor.map_zero, comp_zero]
      intro t
      obtain ⟨s, hs⟩ := hr t
      have ht : t = 0 := by
        rw [hrzero] at hs
        exact hs.symm
      refine ⟨0, ?_⟩
      rw [map_zero, ht]
    · let : IsIso f := proper_integral_restricted_cartier_endomorphism_isIso_of_ne_zero K i P f hf
      have hinj := (ConcreteCategory.bijective_of_isIso
        (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward i).map f) ⊤)).injective
      intro t
      obtain ⟨s, hs⟩ := hr (Scheme.Modules.Hom.app ((Scheme.Modules.pushforward i).map f) ⊤ t)
      refine ⟨s, hinj ?_⟩
      have hs' := hs
      rw [← hfac, Scheme.Modules.Hom.comp_app] at hs'
      exact hs'
  have ht := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback i).obj P.sheaf).presheaf.map (eqToHom i.preimage_top.symm).op)).surjective
  exact ht.comp hη

end MixedFujita
