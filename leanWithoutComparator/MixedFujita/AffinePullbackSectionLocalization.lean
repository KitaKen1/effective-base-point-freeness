/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import SGA.Foundations.Cohomology.BaseChangeSections
public import Mathlib.RingTheory.Localization.BaseChange

/-! Concrete denominator clearing for the actual pullback map on sections.
For affine opens whose ring map is a localization, every pulled section is
a fraction of a source section, and a source section maps to zero exactly
when a denominator annihilates it. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TensorProduct
namespace MixedFujita
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable def pullbackSectionLinearMap {X Y : Scheme.{u}}
    (g : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M), U) where
  toFun := Scheme.Modules.pullbackApp g M U
  map_add' := map_add _
  map_smul' := fun r m ↦ Scheme.Modules.pullbackApp_smul g M U r m

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules) [M.IsQuasicoherent]
  {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U))
  (S : Submonoid Γ(X, U))

include hU hV

theorem affine_pullback_section_exists_denominator :
    let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    IsLocalization S Γ(Y, g ⁻¹ᵁ U) →
    ∀ z : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U),
      ∃ (s : S) (m : Γ(M, U)), g.app U s • z = Scheme.Modules.pullbackApp g M U m := by
  let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  dsimp only
  intro hloc z
  let := hloc
  let e := Scheme.Modules.pullbackSectionsEquiv g M hU hV
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj S
    (TensorProduct.mk Γ(X, U) Γ(Y, g ⁻¹ᵁ U) Γ(M, U) 1) (e z)
  refine ⟨s, m, e.injective ?_⟩
  rw [Scheme.Modules.pullbackSectionsEquiv_smul,
    Scheme.Modules.pullbackSectionsEquiv_pullbackApp]
  rw [Scheme.Hom.app_eq_appLE]
  change (algebraMap Γ(X, U) Γ(Y, g ⁻¹ᵁ U) (s : Γ(X, U))) •
    (e z : Γ(Y, g ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) = (1 : Γ(Y, g ⁻¹ᵁ U)) ⊗ₜ[Γ(X, U)] m
  exact (IsScalarTower.algebraMap_smul
    (M := Γ(Y, g ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U))
    Γ(Y, g ⁻¹ᵁ U) (s : Γ(X, U)) (e z)).trans hs

theorem affine_pullback_section_eq_zero_iff :
    let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    IsLocalization S Γ(Y, g ⁻¹ᵁ U) →
    ∀ m : Γ(M, U), Scheme.Modules.pullbackApp g M U m = 0 ↔ ∃ s : S, (s : Γ(X, U)) • m = 0 := by
  let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  dsimp only
  intro hloc m
  let := hloc
  let e := Scheme.Modules.pullbackSectionsEquiv g M hU hV
  have he : Scheme.Modules.pullbackApp g M U m = 0 ↔
      (TensorProduct.mk Γ(X, U) Γ(Y, g ⁻¹ᵁ U) Γ(M, U) 1) m = 0 := by
    rw [← e.map_eq_zero_iff, Scheme.Modules.pullbackSectionsEquiv_pullbackApp]
    rfl
  rw [he, IsLocalizedModule.eq_zero_iff S]
  rfl

theorem affine_pullback_section_isLocalizedModule :
    let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    IsLocalization S Γ(Y, g ⁻¹ᵁ U) →
      IsLocalizedModule S (pullbackSectionLinearMap g M U) := by
  let : Algebra Γ(X, U) Γ(Y, g ⁻¹ᵁ U) := (g.appLE U (g ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  dsimp only
  intro hloc
  let := hloc
  let : Module Γ(Y, g ⁻¹ᵁ U)
      Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M), U) :=
    inferInstanceAs (Module Γ(Y, g ⁻¹ᵁ U) Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U))
  let e : Γ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M), U) ≃ₗ[Γ(X, U)]
      Γ(Y, g ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U) :=
    { __ := Scheme.Modules.pullbackSectionsEquiv g M hU hV
      map_smul' := fun r z ↦ by
        change Scheme.Modules.pullbackSectionsEquiv g M hU hV
          (g.app U r • (z : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U))) = _
        rw [Scheme.Modules.pullbackSectionsEquiv_smul, Scheme.Hom.app_eq_appLE]
        exact IsScalarTower.algebraMap_smul
          (M := Γ(Y, g ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(M, U)) Γ(Y, g ⁻¹ᵁ U) r _ }
  have he : e.symm.toLinearMap.comp (TensorProduct.mk Γ(X, U) Γ(Y, g ⁻¹ᵁ U) Γ(M, U) 1) =
      (pullbackSectionLinearMap g M U) := by
    ext m
    apply e.injective
    change e (e.symm _) = Scheme.Modules.pullbackSectionsEquiv g M hU hV
      (Scheme.Modules.pullbackApp g M U m)
    rw [LinearEquiv.apply_symm_apply, Scheme.Modules.pullbackSectionsEquiv_pullbackApp]
    rfl
  rw [← he]
  exact IsLocalizedModule.of_linearEquiv S
    (TensorProduct.mk Γ(X, U) Γ(Y, g ⁻¹ᵁ U) Γ(M, U) 1) e.symm

end
end MixedFujita
