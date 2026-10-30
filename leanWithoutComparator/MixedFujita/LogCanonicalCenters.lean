/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogPairOverBasePoint

/-! 実discrepancy素因子を持つlc中心と元非klt点の同定。 See reports/check-255-minimal-valuative-lc-center.json for the verified scope. Actual lc centers carry a proper smooth birational prime of discrepancy exactly -d. Original non-klt points are exactly points in such centers. Mathlib Noetherian closed-set well-foundedness supplies inclusion-minimal centers without classifying all SNC strata or all centers first. One actual SNC model gives a finite center cover of the whole non-klt locus, not a list of all lc centers. Reduced center subschemes are integral. Original positive-numerical normal klt BPF data construct an inclusion-minimal actual lc center, its integral reduced subscheme and strict geometric dimension bound without an initial L section or KV. Center normality, intersections/uniqueness, appropriate center vanishing and restriction lifting/nonvanishing, nu=0, initial L nonvanishing, exterior control/dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- A genuine lc center: the pair is lc on ALL proper smooth birational tests,
and the closed set is the center of a prime with actual discrepancy exactly -d.
No SNC stratum, normality or vanishing is assumed. -/
def LogPairIsLogCanonicalCenter
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (Z : Closeds X) : Prop :=
  LogPairIsLogCanonical c f d D ∧
  ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : IsLocallyNoetherian T)
    (_ : T.Over (Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
    (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cT : EtaleChart K T n) (t : T), Order.coheight t = 1 ∧
      cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t = -(d : ℤ) ∧
      (Z : Set X) = closure ({ρ t} : Set X)


/-- Every actual lc center is irreducible and nonempty. -/
theorem logPairIsLogCanonicalCenter_isIrreducible
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z) :
    IsIrreducible (Z : Set X) := by
  obtain ⟨_, T, _, _, _, _, ρ, _, _, _, hρ, cT, t, _, _, hset⟩ := hZ
  rw [hset]
  exact isIrreducible_singleton.closure


/-- Every point of an actual lc center lies in the ORIGINAL all-model non-klt locus. -/
theorem logPairIsLogCanonicalCenter_not_kltOverBasePoint
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (x : X) (hx : x ∈ Z) :
    ¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D := by
  obtain ⟨_, T, _, _, _, _, ρ, _, _, _, hρ, cT, t, ht, hdiscr, hset⟩ := hZ
  intro hklt
  have hx' : x ∈ closure ({(ρ ≫ 𝟙 X) t} : Set X) := by
    change x ∈ (Z : Set X) at hx
    simpa only [Category.comp_id, hset] using hx
  have h := hklt T ρ hρ cT t ht hx'
  rw [hdiscr] at h
  exact (lt_irrefl _) h


/-- For an lc pair, a non-klt point has an ACTUAL lc center through it.
The witness is extracted directly from failure of the original all-model klt predicate. -/
theorem logCanonical_nonKlt_point_iff_exists_lc_center
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (x : X) :
    (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔
      ∃ Z : Closeds X, LogPairIsLogCanonicalCenter c f d D Z ∧ x ∈ Z := by
  classical
  constructor
  · intro h
    unfold LogPairIsKltOverBasePoint at h
    push Not at h
    obtain ⟨T, _, _, _, _, ρ, _, _, _, hρ, cT, t, ht, hx, hbad⟩ := h
    have hdiscr := le_antisymm hbad (hlc T ρ hρ cT t ht)
    refine ⟨⟨closure ({ρ t} : Set X), isClosed_closure⟩, ?_, ?_⟩
    · exact ⟨hlc, T, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
        inferInstance, inferInstance, inferInstance, hρ, cT, t, ht, hdiscr, rfl⟩
    · change x ∈ closure ({ρ t} : Set X)
      simpa only [Category.comp_id] using hx
  · rintro ⟨Z, hZ, hx⟩
    exact logPairIsLogCanonicalCenter_not_kltOverBasePoint c f d D Z hZ x hx

end MixedFujita
