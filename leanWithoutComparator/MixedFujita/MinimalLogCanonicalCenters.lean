/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenters
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Order.Minimal

/-! Noether閉集合の極小元による実lc中心の存在短縮。 See reports/check-255-minimal-valuative-lc-center.json for the verified scope. Actual lc centers carry a proper smooth birational prime of discrepancy exactly -d. Original non-klt points are exactly points in such centers. Mathlib Noetherian closed-set well-foundedness supplies inclusion-minimal centers without classifying all SNC strata or all centers first. One actual SNC model gives a finite center cover of the whole non-klt locus, not a list of all lc centers. Reduced center subschemes are integral. Original positive-numerical normal klt BPF data construct an inclusion-minimal actual lc center, its integral reduced subscheme and strict geometric dimension bound without an initial L section or KV. Center normality, intersections/uniqueness, appropriate center vanishing and restriction lifting/nonvanishing, nu=0, initial L nonvanishing, exterior control/dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- In a Noetherian source every actual lc center contains an inclusion-minimal
actual lc center. This avoids classifying all SNC strata first. -/
theorem logCanonicalCenter_contains_minimal_center
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z) :
    ∃ W : Closeds X, W ≤ Z ∧ LogPairIsLogCanonicalCenter c f d D W ∧
      ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ W → V = W := by
  obtain ⟨W, hWZ, hW, hmin⟩ :=
    exists_minimal_le_of_wellFoundedLT (LogPairIsLogCanonicalCenter c f d D) Z hZ
  exact ⟨W, hWZ, hW, fun V hV hVW => le_antisymm hVW (hmin hV hVW)⟩


/-- At a non-klt point one can choose a center minimal AMONG centers containing
that point. Uniqueness and intersection-of-centers are not asserted. -/
theorem logCanonical_nonKlt_point_exists_pointwise_minimal_center
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (x : X)
    (hx : ¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) :
    ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f d D W ∧ x ∈ W ∧
      ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → x ∈ V → V ≤ W → V = W := by
  have hex := (logCanonical_nonKlt_point_iff_exists_lc_center c f d D hlc x).mp hx
  obtain ⟨W, ⟨hW, hxW⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun W : Closeds X => LogPairIsLogCanonicalCenter c f d D W ∧ x ∈ W) hex
  exact ⟨W, hW, hxW, fun V hV hxV hVW => le_antisymm hVW (hmin ⟨hV, hxV⟩ hVW)⟩


/-- A non-klt lc pair on a Noetherian source has a genuine inclusion-minimal
lc center, without resolution or a finite-center theorem as input. -/
theorem logCanonical_nonKlt_exists_minimal_center
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (hnot : ¬ LogPairIsKlt c f d D) :
    ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f d D W ∧
      ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ W → V = W := by
  classical
  have h := mt (logPairIsKlt_iff_forall_basePoint (𝟙 X) c f d D).mpr hnot
  push Not at h
  obtain ⟨x, hx⟩ := h
  obtain ⟨Z, hZ, _⟩ := (logCanonical_nonKlt_point_iff_exists_lc_center c f d D hlc x).mp hx
  obtain ⟨W, _, hW, hmin⟩ := logCanonicalCenter_contains_minimal_center c f d D Z hZ
  exact ⟨W, hW, hmin⟩

end MixedFujita
