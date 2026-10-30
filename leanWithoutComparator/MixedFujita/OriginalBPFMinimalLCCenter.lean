/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.OriginalBPFLCSource
public import MixedFujita.MinimalLogCanonicalCenters
public import MixedFujita.LogCanonicalCenterClosedSubscheme
public import MixedFujita.ProperClosedImmersionDimension

/-! 元正ν BPFから初期切断・KVなしの極小整lc中心構成。 See reports/check-255-minimal-valuative-lc-center.json for the verified scope. Actual lc centers carry a proper smooth birational prime of discrepancy exactly -d. Original non-klt points are exactly points in such centers. Mathlib Noetherian closed-set well-foundedness supplies inclusion-minimal centers without classifying all SNC strata or all centers first. One actual SNC model gives a finite center cover of the whole non-klt locus, not a list of all lc centers. Reduced center subschemes are integral. Original positive-numerical normal klt BPF data construct an inclusion-minimal actual lc center, its integral reduced subscheme and strict geometric dimension bound without an initial L section or KV. Center normality, intersections/uniqueness, appropriate center vanishing and restriction lifting/nonvanishing, nu=0, initial L nonvanishing, exterior control/dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Original positive-numerical klt BPF data construct an effective lc non-klt
pair with all-large ample L-adjoints AND a genuine inclusion-minimal lc center.
Its reduced closed subscheme is integral and strictly lower-dimensional.
No initial L-section, KV, supplied center, SNC model or center normality is an input. -/
theorem original_klt_BPF_positive_numerical_exists_minimal_lc_center_without_initial_section
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (L : CartierDivisor X) (hL : CartierIsNef K L)
    (a₀ : ℕ) (hnef : CartierIsNef K ((d * a₀) • L - D))
    (hbig : CartierIsBig K ((d * a₀) • L - D))
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hν : 1 ≤ cartierNumericalDimension K n hdim L J) :
    ∃ r b : ℕ, 1 ≤ r ∧ ∃ D' : CartierDivisor X,
      LogPairBoundaryEffective cX fX r D' ∧ LogPairIsLogCanonical cX fX r D' ∧
      (¬ LogPairIsKlt cX fX r D') ∧
      (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((r * m) • L - D')) ∧
      ∃ Z : Closeds X, LogPairIsLogCanonicalCenter cX fX r D' Z ∧
        (∀ V : Closeds X, LogPairIsLogCanonicalCenter cX fX r D' V → V ≤ Z → V = Z) ∧
        IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ∧
        genericPoint X ∉ (Z : Set X) ∧
        topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (n - 1 : ℕ) := by
  obtain ⟨r, b, hr, D', heff', hlc, hnot, hample, I, _, _, hgen, _, _, _, _, hNK, _, _⟩ :=
    original_klt_BPF_positive_numerical_constructs_canonical_lc_source_without_initial_section
      K n hdim hn hnorm cX fX d hd D heff hklt L hL a₀ hnef hbig J hJ hν
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  let : IsNoetherian X := {}
  obtain ⟨Z, hZ, hmin⟩ := logCanonical_nonKlt_exists_minimal_center cX fX r D' hlc hnot
  have hZI := logCanonicalCenter_le_nonKlt_support cX fX r D' I hNK Z hZ
  have hgenZ : genericPoint X ∉ (Z : Set X) := fun h => hgen (hZI h)
  let Q := Scheme.IdealSheafData.vanishingIdeal Z
  have hsupport : (Q.support : Set X) = Z := Scheme.IdealSheafData.coe_support_vanishingIdeal Z
  have hproper : Set.range Q.subschemeι ≠ Set.univ := by
    intro h
    apply hgenZ
    rw [← hsupport, ← Q.range_subschemeι, h]
    trivial
  have hdimX : topologicalKrullDim X ≤ (n - 1 + 1 : ℕ) := by
    rw [Nat.sub_add_cancel hn]
    exact hdim.le
  have hdimZ := properClosedImmersion_topologicalKrullDim_le_predecessor
    Q.subschemeι hproper (n - 1) hdimX
  exact ⟨r, b, hr, D', heff', hlc, hnot, hample, Z, hZ, hmin,
    logCanonicalCenter_reduced_subscheme_isIntegral cX fX r D' Z hZ, hgenZ, hdimZ⟩

end MixedFujita
