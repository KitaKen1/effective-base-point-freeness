/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantSNCBasePointLogCanonical
public import MixedFujita.HironakaSNCModelExistence

/-!
All-model log-canonicity bounds nonproper smooth birational tests. A proper SNC
model is constructed internally and its non-strict coefficient test controls
actual local extensions. Hence the actual crepant pair is log canonical along
arbitrary birational pullbacks, including open immersions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A proper-model log-canonical condition controls every actual smooth birational test. -/
theorem logPairIsLogCanonical_discrepancy_bound_on_birational_test
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (u : CodimensionOnePoint U) :
    -(d : ℤ) ≤ cartierCoefficient
      (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (u : U) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩ := exists_proper_snc_model c f d D
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  exact crepant_snc_actual_test_logCanonical_bound ρ hρ c f d hd D cT ξ hinj hcoh hsnc hsupp
    (fun i => logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hlc cT ⟨ξ i, hcoh i⟩)
    σ hσ cU u

/-- The base-point guard is preserved for smooth birational tests without properness. -/
theorem logPairIsLogCanonicalOverBasePoint_discrepancy_bound_on_birational_test
    (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonicalOverBasePoint g η c f d D)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (u : CodimensionOnePoint U)
    (hη : η ∈ closure ({(σ ≫ g) (u : U)} : Set Y)) :
    -(d : ℤ) ≤ cartierCoefficient
      (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (u : U) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩ := exists_proper_snc_model c f d D
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  exact crepant_snc_actual_test_logCanonical_bound_overBasePoint ρ hρ g η c f d hd D cT
    ξ hinj hcoh hsnc hsupp
    ((logPairIsLogCanonicalOverBasePoint_iff_crepant_snc_coefficients
      ρ hρ g η c f d hd D cT ξ hinj hcoh hsnc hsupp).mp hlc) σ hσ cU u hη

variable {Z : Scheme.{u}} [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))

/-- Crepant log-canonical ascends along an arbitrary actual birational map, including an open immersion. -/
theorem logPairIsLogCanonical_crepant_pullback_without_properness
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D) (cZ : EtaleChart K Z n) :
    LogPairIsLogCanonical cZ (crepantPullbackFormUnit j hj c f cZ) d (cartierPullback j D) := by
  intro U _ _ _ _ σ _ _ _ hσ cU u hu
  rw [← logDiscrepancyDivisor_comp j σ hj hσ c f d D cZ cU etaleCharts_cover]
  exact logPairIsLogCanonical_discrepancy_bound_on_birational_test c f d hd D hlc
    (σ ≫ j) (dominantFunctionFieldAlgHom_comp_bijective j σ hj hσ) cU ⟨u, hu⟩

/-- Base-point-filtered log-canonical ascends with the actual pulled rational top form. -/
theorem logPairIsLogCanonicalOverBasePoint_crepant_pullback_without_properness
    (g : X ⟶ Y) (η : Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonicalOverBasePoint g η c f d D) (cZ : EtaleChart K Z n) :
    LogPairIsLogCanonicalOverBasePoint (j ≫ g) η cZ (crepantPullbackFormUnit j hj c f cZ) d
      (cartierPullback j D) := by
  intro U _ _ _ _ σ _ _ _ hσ cU u hu hη
  rw [← logDiscrepancyDivisor_comp j σ hj hσ c f d D cZ cU etaleCharts_cover]
  apply logPairIsLogCanonicalOverBasePoint_discrepancy_bound_on_birational_test g η c f d hd D hlc
    (σ ≫ j) (dominantFunctionFieldAlgHom_comp_bijective j σ hj hσ) cU ⟨u, hu⟩
  simpa only [Category.assoc] using hη

end MixedFujita
