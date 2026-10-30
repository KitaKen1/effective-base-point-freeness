/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.OriginalBPFLCAmplePair
public import MixedFujita.LCNonKltClosedSubscheme
public import MixedFujita.NormalCodimensionOneCharts
public import MixedFujita.CartierBigDefinition
public import MixedFujita.CartierNefDefinition

/-! 元正ν BPFから初期切断・KVなしの標準非空被約低次元W。 See reports/check-254-positive-numerical-lc-ample-source.json for the verified scope. Actual non-lc concentration internally gives a strictly smaller rational effective lc non-klt endpoint. Actual Cartier decomposition preserves an ample original L-adjoint in every large degree. Original normal klt BPF data with positive original numerical dimension construct a canonical nonempty reduced lower-dimensional non-klt source without an initial L section or KV; codimension-one charts follow internally from normality. The same source has all-large-original-L restriction lifting under explicit usual H1 KV. Initial and positive-dimensional restricted nonvanishing, minimal lc-center geometry, center-exterior control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- ORIGINAL normal klt BPF data of positive ORIGINAL numerical dimension
construct a canonical nonempty reduced lower-dimensional non-klt source, WITHOUT
an initial L-section and WITHOUT KV. All large L-adjoints are AMPLE. Only the
original L restriction lifting is conditional on explicit usual H1 KV. -/
theorem original_klt_BPF_positive_numerical_constructs_canonical_lc_source_without_initial_section
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
      ∃ I : X.IdealSheafData, I ≠ ⊥ ∧ Nonempty I.subscheme ∧
        genericPoint X ∉ (I.support : Set X) ∧
        topologicalKrullDim I.subscheme ≤ (n - 1 : ℕ) ∧
        (idealSheafDataModule I).IsCoherent ∧ I.radical = I ∧ IsReduced I.subscheme ∧
        (∀ x : X, x ∈ (I.support : Set X) ↔
          ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX r D') ∧
        (∀ Q : X.IdealSheafData, Q.radical = Q →
          (∀ x : X, x ∈ (Q.support : Set X) ↔
            ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX r D') → Q = I) ∧
        ∀ (_ : KawamataViehwegVanishingSNC K n), ∀ m : ℕ, b ≤ m →
          Subsingleton (Scheme.Modules.Cohomology ((m • L).sheaf ⊗ idealSheafDataModule I) 1) ∧
          ∃ ρ : (m • L).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
              ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf),
            Function.Surjective (Scheme.Modules.Hom.app ρ ⊤) ∧
            ∀ t : Γ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf, ⊤), t ≠ 0 →
              ∃ x : X, x ∈ (I.support : Set X) ∧ x ∉ cartierBaseLocus (m • L) := by
  obtain ⟨r, b, hr, D', heff', hlc, hnot, _, hample⟩ :=
    original_klt_BPF_positive_numerical_exists_lc_nonKlt_ample_adjoint_pair K n hdim hn hnorm
      cX fX d hd D heff hklt L hL a₀ hnef hbig J hJ hν
  have hcov : CodimOneChartCovered n K X := normal_codimOneChartCovered (K := K) hdim hnorm
  obtain ⟨I, hI, hW, hgen, hdimW, hcoh, hIr, hred, _, hNK, hUnique, _, hLift⟩ :=
    lc_pair_exists_unique_reduced_nonKlt_subscheme K hn hnorm hcov ⟨J, hJ⟩
      cX fX r hr D' heff' hlc hnot
  refine ⟨r, b, hr, D', heff', hlc, hnot, hample, I, hI, hW, hgen, hdimW, hcoh, hIr,
    hred, hNK, hUnique, ?_⟩
  intro hKV m hm
  have hA : CartierIsAmpleProj K (r • (m • L) - D') := by
    simpa only [smul_smul] using hample m hm
  exact hLift hKV (m • L) (cartierIsAmpleProj_isNef hA) (cartierIsAmpleProj_isBig hdim hn hA)

end MixedFujita
