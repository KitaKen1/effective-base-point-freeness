/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalQuotientAffineSections
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! The structure-sheaf quotient tower on an affine chart is the actual
ring quotient tower by powers of the extended base ideal. Kernel evaluation
and compatible linear equivalences are exposed with their inclusion formulas. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable def moduleKernelSectionsEquiv {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) :
    Γ(kernel φ, U) ≃ₗ[Γ(X, U)] LinearMap.ker (appLinearMap φ U) :=
  ((asIso (kernelComparison φ (moduleOpenEvaluation X U))) ≪≫
    ModuleCat.kernelIsoKer ((moduleOpenEvaluation X U).map φ)).toLinearEquiv

theorem moduleKernelSectionsEquiv_val {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) (x : Γ(kernel φ, U)) :
    (moduleKernelSectionsEquiv φ U x).val = (kernel.ι φ).app U x := by
  have h := congrArg (fun k => k x)
    (show kernelComparison φ (moduleOpenEvaluation X U) ≫
        (ModuleCat.kernelIsoKer ((moduleOpenEvaluation X U).map φ)).hom ≫
          ModuleCat.ofHom (((moduleOpenEvaluation X U).map φ).hom.ker.subtype) =
        (moduleOpenEvaluation X U).map (kernel.ι φ) by
      rw [ModuleCat.kernelIsoKer_hom_ker_subtype, kernelComparison_comp_ι])
  exact h

/-- Restrict compatible linear equivalences to their actual kernels. -/
noncomputable def linearKernelEquivOfSquare
    {R M N M' N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (a : M ≃ₗ[R] M') (b : N ≃ₗ[R] N')
    (h : ∀ x, g (a x) = b (f x)) : LinearMap.ker f ≃ₗ[R] LinearMap.ker g :=
  a.ofSubmodules _ _ (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change g (a x) = 0
      rw [h, LinearMap.mem_ker.mp hx, map_zero]
    · intro hy
      obtain ⟨x, rfl⟩ := a.surjective y
      refine ⟨x, ?_, rfl⟩
      apply b.injective
      simpa only [map_zero, ← h] using (LinearMap.mem_ker.mp hy))

theorem linearKernelEquivOfSquare_val
    {R M N M' N' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (a : M ≃ₗ[R] M') (b : N ≃ₗ[R] N')
    (h : ∀ x, g (a x) = b (f x)) (x : LinearMap.ker f) :
    (linearKernelEquivOfSquare f g a b h x).val = a x.val := rfl

variable {A : CommRingCat.{u}} [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A) (I : Ideal A)

theorem unitInfinitesimalQuotientAffine_ker (U : X.affineOpens) (n : ℕ) :
    LinearMap.ker (appLinearMap ((unitModule X).toQuotientIdealPow f I n) U.1) =
      (I.map (structMapV f U.1)) ^ (n + 1) := by
  simpa only [idealV, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow] using
    infinitesimalQuotientAffine_ker f I (unitModule X) U n

noncomputable def unitInfinitesimalQuotientAffineEquiv (U : X.affineOpens) (n : ℕ) :
    (Γ(X, U.1) ⧸ (I.map (structMapV f U.1)) ^ (n + 1)) ≃ₗ[Γ(X, U.1)]
      Γ((unitModule X).quotientIdealPow f I n, U.1) :=
  (Submodule.quotEquivOfEq _ _ (unitInfinitesimalQuotientAffine_ker f I U n).symm).trans
    ((appLinearMap ((unitModule X).toQuotientIdealPow f I n) U.1).quotKerEquivOfSurjective
      (toQuotientIdealPow_app_surjective I f n U.2))

theorem unitInfinitesimalQuotientAffineEquiv_mk (U : X.affineOpens) (n : ℕ)
    (x : Γ(X, U.1)) :
    unitInfinitesimalQuotientAffineEquiv f I U n (Submodule.Quotient.mk x) =
      ((unitModule X).toQuotientIdealPow f I n).app U.1 x := rfl

/-- Naturality for the actual adjacent transition, on all quotient elements. -/
theorem unitInfinitesimalQuotientAffineEquiv_transition (U : X.affineOpens) (n : ℕ)
    (x : Γ(X, U.1) ⧸ (I.map (structMapV f U.1)) ^ (n + 1 + 1)) :
    ((unitModule X).quotientIdealPowMap f I n).app U.1
        (unitInfinitesimalQuotientAffineEquiv f I U (n + 1) x) =
      unitInfinitesimalQuotientAffineEquiv f I U n
        (Submodule.factor (Ideal.pow_le_pow_right (I := I.map (structMapV f U.1))
          (Nat.le_succ (n + 1))) x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change ((unitModule X).quotientIdealPowMap f I n).app U.1
      (((unitModule X).toQuotientIdealPow f I (n + 1)).app U.1 a) =
    ((unitModule X).toQuotientIdealPow f I n).app U.1 a
  change (((unitModule X).toQuotientIdealPow f I (n + 1) ≫
    (unitModule X).quotientIdealPowMap f I n).app U.1) a = _
  rw [Scheme.Modules.toQuotientIdealPow_comp_map]

end MixedFujita
