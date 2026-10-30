/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.UnitInfinitesimalAffineComparison
public import MixedFujita.RegularPrincipalInfinitesimalLayer
public import MixedFujita.IdealSheafAffineModulePresentation

/-! Affine presentations of the actual infinitesimal kernel sheaves.
The canonical comparison respects the kernel inclusion. A regular local
equation identifies every layer with the associated sheaf of the first
quotient, with multiplication by the appropriate power as its formula. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A : CommRingCat.{u}} [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A) (I : Ideal A)

/-- The actual ring kernel maps to sections of the actual sheaf kernel. -/
noncomputable def unitInfinitesimalLayerAffineSectionsEquiv (U : X.affineOpens) (n : ℕ) :
    LinearMap.ker (Submodule.factor
      (Ideal.pow_le_pow_right (I := I.map (structMapV f U.1)) (Nat.le_succ (n + 1))))
      ≃ₗ[Γ(X, U.1)] Γ(infinitesimalCohomologyLayer f I (unitModule X) n, U.1) :=
  (linearKernelEquivOfSquare _
    (appLinearMap ((unitModule X).quotientIdealPowMap f I n) U.1)
    (unitInfinitesimalQuotientAffineEquiv f I U (n + 1))
    (unitInfinitesimalQuotientAffineEquiv f I U n)
    (unitInfinitesimalQuotientAffineEquiv_transition f I U n)).trans
      (moduleKernelSectionsEquiv ((unitModule X).quotientIdealPowMap f I n) U.1).symm

theorem unitInfinitesimalLayerAffineSectionsEquiv_inclusion (U : X.affineOpens) (n : ℕ)
    (x : LinearMap.ker (Submodule.factor
      (Ideal.pow_le_pow_right (I := I.map (structMapV f U.1)) (Nat.le_succ (n + 1))))) :
    (kernel.ι ((unitModule X).quotientIdealPowMap f I n)).app U.1
        (unitInfinitesimalLayerAffineSectionsEquiv f I U n x) =
      unitInfinitesimalQuotientAffineEquiv f I U (n + 1) x.val := by
  rw [← moduleKernelSectionsEquiv_val]
  change ((moduleKernelSectionsEquiv _ U.1)
    ((moduleKernelSectionsEquiv _ U.1).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- No layer presentation is an input: a principal regular equation suffices. -/
noncomputable def unitInfinitesimalLayerRegularSectionsEquiv (U : X.affineOpens)
    (t : Γ(X, U.1)) (hI : I.map (structMapV f U.1) = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors Γ(X, U.1)) (n : ℕ) :
    (Γ(X, U.1) ⧸ I.map (structMapV f U.1)) ≃ₗ[Γ(X, U.1)]
      Γ(infinitesimalCohomologyLayer f I (unitModule X) n, U.1) :=
  (regularPrincipalIdealLayerEquiv (I.map (structMapV f U.1)) t hI ht (n + 1)).trans
    (unitInfinitesimalLayerAffineSectionsEquiv f I U n)

theorem unitInfinitesimalLayerRegularSectionsEquiv_inclusion_mk (U : X.affineOpens)
    (t : Γ(X, U.1)) (hI : I.map (structMapV f U.1) = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors Γ(X, U.1)) (n : ℕ) (x : Γ(X, U.1)) :
    (kernel.ι ((unitModule X).quotientIdealPowMap f I n)).app U.1
        (unitInfinitesimalLayerRegularSectionsEquiv f I U t hI ht n
          (Submodule.Quotient.mk x)) =
      ((unitModule X).toQuotientIdealPow f I (n + 1)).app U.1 (t ^ (n + 1) * x) := by
  change (kernel.ι ((unitModule X).quotientIdealPowMap f I n)).app U.1
    (unitInfinitesimalLayerAffineSectionsEquiv f I U n
      (regularPrincipalIdealLayerEquiv _ t hI ht (n + 1) (Submodule.Quotient.mk x))) = _
  rw [unitInfinitesimalLayerAffineSectionsEquiv_inclusion,
    regularPrincipalIdealLayerEquiv_mk, unitInfinitesimalQuotientAffineEquiv_mk]

/-- Changing the regular equation by a unit changes actual layer coordinates
by the corresponding power, as an equality of actual sheaf sections. -/
theorem unitInfinitesimalLayerRegularSectionsEquiv_change_equation (U : X.affineOpens)
    (t : Γ(X, U.1)) (u : Γ(X, U.1)ˣ)
    (hI : I.map (structMapV f U.1) = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors Γ(X, U.1)) (n : ℕ)
    (x : Γ(X, U.1) ⧸ I.map (structMapV f U.1)) :
    unitInfinitesimalLayerRegularSectionsEquiv f I U ((u : Γ(X, U.1)) * t)
        (hI.trans (Ideal.span_singleton_mul_left_unit u.isUnit t).symm)
        (mul_mem u.isUnit.mem_nonZeroDivisors ht) n x =
      unitInfinitesimalLayerRegularSectionsEquiv f I U t hI ht n
        ((u : Γ(X, U.1)) ^ (n + 1) • x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  apply (moduleKernelSectionsEquiv ((unitModule X).quotientIdealPowMap f I n) U.1).injective
  apply Subtype.ext
  simp only [moduleKernelSectionsEquiv_val]
  change (kernel.ι ((unitModule X).quotientIdealPowMap f I n)).app U.1
      (unitInfinitesimalLayerRegularSectionsEquiv f I U _ _ _ n
        (Submodule.Quotient.mk a)) =
    (kernel.ι ((unitModule X).quotientIdealPowMap f I n)).app U.1
      (unitInfinitesimalLayerRegularSectionsEquiv f I U t hI ht n
        (Submodule.Quotient.mk ((u : Γ(X, U.1)) ^ (n + 1) * a)))
  rw [unitInfinitesimalLayerRegularSectionsEquiv_inclusion_mk,
    unitInfinitesimalLayerRegularSectionsEquiv_inclusion_mk]
  congr 1
  simp only [mul_pow, mul_assoc, mul_left_comm]

/-- The actual quotient sheaf restricted to an affine chart. -/
noncomputable def unitInfinitesimalQuotientAffineSheafIso (U : X.affineOpens) (n : ℕ) :
    ((unitModule X).quotientIdealPow f I n).restrict U.2.fromSpec ≅
      tilde (ModuleCat.of Γ(X, U.1)
        (Γ(X, U.1) ⧸ (I.map (structMapV f U.1)) ^ (n + 1))) := by
  let := infinitesimalQuotient_isQuasicoherent f I (unitModule X) n
  exact moduleAffineTildeIso _ U ≪≫
    (tilde.functor Γ(X, U.1)).mapIso
      (unitInfinitesimalQuotientAffineEquiv f I U n).symm.toModuleIso

/-- The actual kernel sheaf is the sheaf associated to the actual ring kernel. -/
noncomputable def unitInfinitesimalLayerAffineSheafIso (U : X.affineOpens) (n : ℕ) :
    (infinitesimalCohomologyLayer f I (unitModule X) n).restrict U.2.fromSpec ≅
      tilde (ModuleCat.of Γ(X, U.1) (LinearMap.ker (Submodule.factor
        (Ideal.pow_le_pow_right (I := I.map (structMapV f U.1)) (Nat.le_succ (n + 1)))))) := by
  let := infinitesimalLayer_isQuasicoherent f I (unitModule X) n
  exact moduleAffineTildeIso _ U ≪≫
    (tilde.functor Γ(X, U.1)).mapIso
      (unitInfinitesimalLayerAffineSectionsEquiv f I U n).symm.toModuleIso

/-- A regular equation gives a genuine affine sheaf isomorphism for every layer. -/
noncomputable def unitInfinitesimalLayerRegularSheafIso (U : X.affineOpens)
    (t : Γ(X, U.1)) (hI : I.map (structMapV f U.1) = Ideal.span {t})
    (ht : t ∈ nonZeroDivisors Γ(X, U.1)) (n : ℕ) :
    (infinitesimalCohomologyLayer f I (unitModule X) n).restrict U.2.fromSpec ≅
      tilde (ModuleCat.of Γ(X, U.1) (Γ(X, U.1) ⧸ I.map (structMapV f U.1))) := by
  let := infinitesimalLayer_isQuasicoherent f I (unitModule X) n
  exact moduleAffineTildeIso _ U ≪≫
    (tilde.functor Γ(X, U.1)).mapIso
      (unitInfinitesimalLayerRegularSectionsEquiv f I U t hI ht n).symm.toModuleIso

end MixedFujita
