/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.OriginalBPFNonLCConcentration
public import MixedFujita.ConcentrationLCEndpoint
public import MixedFujita.ConcentrationLCAmpleAdjoint

/-! 元正ν BPFから初期切断なしの有効lc非klt ample随伴対。 See reports/check-254-positive-numerical-lc-ample-source.json for the verified scope. Actual non-lc concentration internally gives a strictly smaller rational effective lc non-klt endpoint. Actual Cartier decomposition preserves an ample original L-adjoint in every large degree. Original normal klt BPF data with positive original numerical dimension construct a canonical nonempty reduced lower-dimensional non-klt source without an initial L section or KV; codimension-one charts follow internally from normality. The same source has all-large-original-L restriction lifting under explicit usual H1 KV. Initial and positive-dimensional restricted nonvanishing, minimal lc-center geometry, center-exterior control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- ORIGINAL normal klt BPF data with positive ORIGINAL numerical dimension
construct an effective lc non-klt pair with an AMPLE L-adjoint in every sufficiently
large original degree. No original L-section, KV, threshold or model is supplied. -/
theorem original_klt_BPF_positive_numerical_exists_lc_nonKlt_ample_adjoint_pair
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
      CartierIsAmpleProj K ((r * b) • L - D') ∧
      ∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((r * m) • L - D') := by
  obtain ⟨s, hs, G, hG, heff₀, hklt₀, hA, x, hxcl, _, hxc, hDx, j, hj, hcuts⟩ :=
    original_klt_BPF_positive_numerical_exists_effective_concentration_nonLC_point K n hdim hn hnorm
      cX fX d hd D heff hklt L hL a₀ hnef hbig J hJ hν ⊤
      ⟨⟨genericPoint X, Opens.mem_top _⟩⟩
  obtain ⟨M, hM, ⟨u, hlinear⟩, _, hbad⟩ := hcuts j le_rfl
  have hsd : 1 ≤ s * d := by nlinarith
  obtain ⟨a, q, ha, hq, hsmall, heff', hlc, hnot⟩ :=
    effective_nonLC_concentration_exists_strictly_smaller_lc_endpoint hnorm cX fX (s * d) hsd
      (s • D + G) heff₀ hklt₀ M hM j hj x hbad
  let l := n.factorial * (n * (s * d) + 1) ^ n + 1
  let b := a₀ + a * j * l
  have hamp := concentration_lc_perturbed_adjoint_isAmple K L (s • D + G) M hL
    (s * d) a₀ a q j l hsmall hA u hlinear
  have hdenom : 1 ≤ q * (s * d) := Nat.mul_pos (by omega) (by omega)
  exact ⟨q * (s * d), b, hdenom, q • (s • D + G) + ((s * d) * a) • M,
    heff', hlc, hnot, hamp, original_nef_ample_adjoint_all_large K L _ hL _ b hamp⟩

end MixedFujita
