/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalQuotientAffineSections
public import MixedFujita.UnitInfinitesimalAffineComparison

/-! Global associated-graded presentation of the actual infinitesimal layers.
The canonical map from I^(n+1)M onto the actual kernel has kernel I^(n+2)M.
Its cokernel presentation is constructed globally, with no local gluing data
or regular equation as an input. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem moduleMonomorphism_app_injective {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) [Mono φ] (U : X.Opens) : Function.Injective (φ.app U) :=
  (ModuleCat.mono_iff_injective ((moduleOpenEvaluation X U).map φ)).mp
    ((moduleOpenEvaluation X U).map_mono φ)

variable {A : CommRingCat.{u}} [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A) (I : Ideal A) (M : X.Modules)

theorem idealPower_isQuasicoherent [M.IsQuasicoherent] (n : ℕ) :
    (IPow f I M n).IsQuasicoherent := by
  let : (⨁ fun _ : Fin (numGens I n) => M).IsQuasicoherent := isQuasicoherent_biproduct _
  exact isQuasicoherent_image (powMap f I M n)

noncomputable def idealPowerToInfinitesimalLayer (n : ℕ) :
    IPow f I M (n + 1) ⟶ infinitesimalCohomologyLayer f I M n :=
  kernel.lift (M.quotientIdealPowMap f I n)
    (ιPow f I M (n + 1) ≫ M.toQuotientIdealPow f I (n + 1)) (by
      rw [Category.assoc, M.toQuotientIdealPow_comp_map, ιPow_toQuotientIdealPow])

@[reassoc (attr := simp)]
theorem idealPowerToInfinitesimalLayer_inclusion (n : ℕ) :
    idealPowerToInfinitesimalLayer f I M n ≫ kernel.ι (M.quotientIdealPowMap f I n) =
      ιPow f I M (n + 1) ≫ M.toQuotientIdealPow f I (n + 1) :=
  kernel.lift_ι _ _ _

theorem inclPow_toInfinitesimalLayer (n : ℕ) :
    inclPow f I M (Nat.le_succ (n + 1)) ≫ idealPowerToInfinitesimalLayer f I M n = 0 := by
  apply (cancel_mono (kernel.ι (M.quotientIdealPowMap f I n))).mp
  rw [Category.assoc, idealPowerToInfinitesimalLayer_inclusion,
    ← Category.assoc, inclPow_ιPow, ιPow_toQuotientIdealPow, zero_comp]

noncomputable def idealPowerLayerShortComplex (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (inclPow f I M (Nat.le_succ (n + 1)))
    (idealPowerToInfinitesimalLayer f I M n) (inclPow_toInfinitesimalLayer f I M n)

theorem idealPowerToInfinitesimalLayer_app_surjective [M.IsQuasicoherent]
    (U : X.affineOpens) (n : ℕ) :
    Function.Surjective ((idealPowerToInfinitesimalLayer f I M n).app U.1) := by
  intro z
  obtain ⟨x, hx⟩ := toQuotientIdealPow_app_surjective I f (n + 1) U.2
    ((kernel.ι (M.quotientIdealPowMap f I n)).app U.1 z)
  have hx0 : (M.toQuotientIdealPow f I n).app U.1 x = 0 := by
    rw [← M.toQuotientIdealPow_comp_map f I n]
    change (M.quotientIdealPowMap f I n).app U.1
      ((M.toQuotientIdealPow f I (n + 1)).app U.1 x) = 0
    rw [hx]
    exact congrArg (fun k : infinitesimalCohomologyLayer f I M n ⟶ M.quotientIdealPow f I n =>
      k.app U.1 z) (kernel.condition (M.quotientIdealPowMap f I n))
  obtain ⟨y, hy⟩ := (toQuotientIdealPow_app_eq_zero_iff I f M n U.1 x).mp hx0
  refine ⟨y, ?_⟩
  apply moduleMonomorphism_app_injective (kernel.ι (M.quotientIdealPowMap f I n)) U.1
  change ((idealPowerToInfinitesimalLayer f I M n ≫
    kernel.ι (M.quotientIdealPowMap f I n)).app U.1) y = _
  rw [idealPowerToInfinitesimalLayer_inclusion]
  change (M.toQuotientIdealPow f I (n + 1)).app U.1 ((ιPow f I M (n + 1)).app U.1 y) = _
  rw [hy, hx]

theorem idealPowerLayerShortComplex_shortExact [M.IsQuasicoherent] (n : ℕ) :
    (idealPowerLayerShortComplex f I M n).ShortExact := by
  let : Mono (inclPow f I M (Nat.le_succ (n + 1))) :=
    mono_of_mono_fac (inclPow_ιPow f I M (Nat.le_succ (n + 1)))
  apply moduleShortComplex_shortExact_of_affine_evaluation
  intro U
  let S := (idealPowerLayerShortComplex f I M n).map (moduleOpenEvaluation X U.1)
  have hf : Mono S.f := (moduleOpenEvaluation X U.1).map_mono
    (inclPow f I M (Nat.le_succ (n + 1)))
  have hg : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr
    (idealPowerToInfinitesimalLayer_app_surjective f I M U n)
  apply ShortComplex.ShortExact.mk' (S := S) _ hf hg
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  have h0 : (M.toQuotientIdealPow f I (n + 1)).app U.1
      ((ιPow f I M (n + 1)).app U.1 y) = 0 := by
    have h := congrArg (fun k : IPow f I M (n + 1) ⟶ M.quotientIdealPow f I (n + 1) =>
      k.app U.1 y) (idealPowerToInfinitesimalLayer_inclusion f I M n)
    change (kernel.ι (M.quotientIdealPowMap f I n)).app U.1
      ((idealPowerToInfinitesimalLayer f I M n).app U.1 y) = _ at h
    rw [show (idealPowerToInfinitesimalLayer f I M n).app U.1 y = 0 from hy, map_zero] at h
    exact h.symm
  obtain ⟨z, hz⟩ := (toQuotientIdealPow_app_eq_zero_iff I f M (n + 1) U.1 _).mp h0
  refine ⟨z, ?_⟩
  apply moduleMonomorphism_app_injective (ιPow f I M (n + 1)) U.1
  change ((inclPow f I M (Nat.le_succ (n + 1)) ≫ ιPow f I M (n + 1)).app U.1) z = _
  rw [inclPow_ιPow]
  exact hz

/-- A global, canonical associated-graded presentation of the actual kernel. -/
noncomputable def infinitesimalLayerIdealPowerQuotientIso [M.IsQuasicoherent] (n : ℕ) :
    cokernel (inclPow f I M (Nat.le_succ (n + 1))) ≅
      infinitesimalCohomologyLayer f I M n :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (idealPowerLayerShortComplex_shortExact f I M n).gIsCokernel

@[reassoc (attr := simp)]
theorem infinitesimalLayerIdealPowerQuotientIso_π [M.IsQuasicoherent] (n : ℕ) :
    cokernel.π (inclPow f I M (Nat.le_succ (n + 1))) ≫
        (infinitesimalLayerIdealPowerQuotientIso f I M n).hom =
      idealPowerToInfinitesimalLayer f I M n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (idealPowerLayerShortComplex_shortExact f I M n).gIsCokernel WalkingParallelPair.one

end MixedFujita
