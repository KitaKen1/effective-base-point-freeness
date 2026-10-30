/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenters
public import MixedFujita.CrepantSNCBasePointKlt
public import MixedFujita.CrepantSNCBasePointLogCanonical

/-! 実SNC臨界素因子による全非klt locusの有限lc中心被覆。 See reports/check-255-minimal-valuative-lc-center.json for the verified scope. Actual lc centers carry a proper smooth birational prime of discrepancy exactly -d. Original non-klt points are exactly points in such centers. Mathlib Noetherian closed-set well-foundedness supplies inclusion-minimal centers without classifying all SNC strata or all centers first. One actual SNC model gives a finite center cover of the whole non-klt locus, not a list of all lc centers. Reduced center subschemes are integral. Original positive-numerical normal klt BPF data construct an inclusion-minimal actual lc center, its integral reduced subscheme and strict geometric dimension bound without an initial L section or KV. Center normality, intersections/uniqueness, appropriate center vanishing and restriction lifting/nonvanishing, nu=0, initial L nonvanishing, exterior control/dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- A coefficient-d prime of an actual crepant model gives a genuine lc center
of the original pair, with the actual proper birational model as witness. -/
theorem crepant_critical_prime_is_logCanonicalCenter
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (cT : EtaleChart K T n)
    (t : T) (ht : Order.coheight t = 1)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) t = d) :
    LogPairIsLogCanonicalCenter c f d D ⟨closure ({ρ t} : Set X), isClosed_closure⟩ := by
  refine ⟨hlc, T, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
    inferInstance, inferInstance, inferInstance, hρ, cT, t, ht, ?_, rfl⟩
  rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg] at hcrit
  omega


/-- The original non-klt locus is covered by finitely many genuine lc centers
coming from the coefficient-d primes of ONE actual SNC model. This does not
claim that all lc centers occur among these divisorial images. -/
theorem crepant_snc_nonKlt_finite_actual_lc_center_cover
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0) :
    ∃ S : Finset (Fin r),
      (∀ i, i ∈ S ↔ cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = d) ∧
      (∀ i ∈ S, LogPairIsLogCanonicalCenter c f d D
        ⟨closure ({ρ (ξ i)} : Set X), isClosed_closure⟩) ∧
      ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔
        ∃ i ∈ S, x ∈ closure ({ρ (ξ i)} : Set X) := by
  classical
  let S := Finset.univ.filter (fun i => cartierCoefficient
    (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = d)
  have hS (i : Fin r) : i ∈ S ↔ cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = d := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨S, hS, ?_, ?_⟩
  · intro i hi
    exact crepant_critical_prime_is_logCanonicalCenter ρ hρ c f d D hlc cT (ξ i) (hξ i) ((hS i).mp hi)
  · intro x
    rw [logPairIsKltOverBasePoint_iff_crepant_snc_coefficients ρ hρ (𝟙 X) x
      c f d hd D cT ξ hinj hξ hsnc hsupport]
    simp only [Category.comp_id]
    push Not
    constructor
    · rintro ⟨i, hxi, hbad⟩
      have hb := logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hlc cT ⟨ξ i, hξ i⟩
      exact ⟨i, (hS i).mpr (le_antisymm hb hbad), hxi⟩
    · rintro ⟨i, hi, hx⟩
      exact ⟨i, hx, ((hS i).mp hi).ge⟩

end MixedFujita
