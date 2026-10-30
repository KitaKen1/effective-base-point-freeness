/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleAffineExactness
public import MixedFujita.InfinitesimalCohomologyLayers
public import SGA.Foundations.Cohomology.SeparatingSections
public import Mathlib.LinearAlgebra.Isomorphisms

/-! Affine sections of the actual SGA infinitesimal quotient, with the
canonical quotient map and transition maps. Quasi-coherence of the actual
quotients and their successive kernels is proved from the finite-generator
presentation, rather than required separately. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A : CommRingCat.{u}} [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A) (I : Ideal A) (M : X.Modules) [M.IsQuasicoherent]

theorem infinitesimalQuotient_isQuasicoherent (n : ℕ) :
    (M.quotientIdealPow f I n).IsQuasicoherent := by
  let : (⨁ fun _ : Fin (numGens I (n + 1)) => M).IsQuasicoherent :=
    isQuasicoherent_biproduct _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (cokernelPowMapIso f I M n) (isQuasicoherent_cokernel (powMap f I M (n + 1)))

theorem infinitesimalLayer_isQuasicoherent (n : ℕ) :
    (infinitesimalCohomologyLayer f I M n).IsQuasicoherent := by
  let := infinitesimalQuotient_isQuasicoherent f I M n
  let := infinitesimalQuotient_isQuasicoherent f I M (n + 1)
  exact isQuasicoherent_kernel (M.quotientIdealPowMap f I n)

theorem infinitesimalQuotientAffine_ker (U : X.affineOpens) (n : ℕ) :
    LinearMap.ker (appLinearMap (M.toQuotientIdealPow f I n) U.1) =
      idealV f I U.1 (n + 1) • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  ext x
  change (M.toQuotientIdealPow f I n).app U.1 x = 0 ↔ _
  rw [toQuotientIdealPow_app_eq_zero_iff, mem_range_ιPow_app f I M U.2]

/-- The first isomorphism theorem applied to the actual quotient on an affine open. -/
noncomputable def infinitesimalQuotientAffineSectionsEquiv (U : X.affineOpens) (n : ℕ) :
    (Γ(M, U.1) ⧸ (idealV f I U.1 (n + 1) • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1))))
      ≃ₗ[Γ(X, U.1)] Γ(M.quotientIdealPow f I n, U.1) :=
  (Submodule.quotEquivOfEq _ _ (infinitesimalQuotientAffine_ker f I M U n).symm).trans
    ((appLinearMap (M.toQuotientIdealPow f I n) U.1).quotKerEquivOfSurjective
      (toQuotientIdealPow_app_surjective I f n U.2))

theorem infinitesimalQuotientAffineSectionsEquiv_mk (U : X.affineOpens)
    (n : ℕ) (x : Γ(M, U.1)) :
    infinitesimalQuotientAffineSectionsEquiv f I M U n (Submodule.Quotient.mk x) =
      (M.toQuotientIdealPow f I n).app U.1 x := rfl

theorem infinitesimalQuotientAffineSectionsEquiv_transition_mk (U : X.affineOpens)
    (n : ℕ) (x : Γ(M, U.1)) :
    (M.quotientIdealPowMap f I n).app U.1
        (infinitesimalQuotientAffineSectionsEquiv f I M U (n + 1)
          (Submodule.Quotient.mk x)) =
      infinitesimalQuotientAffineSectionsEquiv f I M U n (Submodule.Quotient.mk x) := by
  simp only [infinitesimalQuotientAffineSectionsEquiv_mk]
  change ((M.toQuotientIdealPow f I (n + 1) ≫ M.quotientIdealPowMap f I n).app U.1) x = _
  rw [M.toQuotientIdealPow_comp_map f I n]

end MixedFujita
