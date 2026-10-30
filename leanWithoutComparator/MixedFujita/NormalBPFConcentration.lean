/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SmoothLocusNefPencilConcentration
public import MixedFujita.NefNumericalDimensionAmpleIndependence
public import MixedFujita.BPFKodairaAmpleBoundary

/-! 元正規klt BPFから全体smooth仮定なしの正規化集中因子。 See reports/check-253-singular-concentration-nonLC-point.json for the verified scope. Actual etale chart completions evaluate original global Cartier sections on a possibly singular integral source, without global smoothness. Original normal klt BPF data with positive numerical dimension construct all-high-power concentrated effective divisors at smooth closed points, without an initial L section or KV. Actual high regular-equation order obstructs the original all-model pointwise log-canonical and klt predicates. A boundary-free closed point in any nonempty open and effective non-lc perturbations are constructed internally. Initial and restricted nonvanishing, lc-threshold ample preservation, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower


/-- ORIGINAL normal klt BPF nef-big data with positive ORIGINAL numerical
dimension on a possibly singular source construct a small effective klt boundary, an ample adjoint pencil,
and actual concentration cuts of normalized multiplicity greater than n.
The initial L-section, concentration cut and usual KV are all absent inputs. -/
theorem original_normal_klt_BPF_positive_numerical_constructs_normalized_concentration
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
    ∃ s : ℕ, 2 ≤ s ∧ ∃ G : CartierDivisor X, G.IsEffective ∧
      LogPairBoundaryEffective cX fX (s * d) (s • D + G) ∧
      LogPairIsKlt cX fX (s * d) (s • D + G) ∧
      CartierIsAmpleProj K (((s * d) * a₀) • L - (s • D + G)) ∧
      let l := n.factorial * (n * (s * d) + 1) ^ n + 1
      CartierIsAmpleProj K ((l + (s * d) * a₀) • L - (s • D + G)) ∧
        ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∀ x : X, IsClosed {x} → x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus →
          ∃ M : CartierDivisor X, M.IsEffective ∧
            (∃ u : X.functionFieldˣ,
              M = j • ((l + (s * d) * a₀) • L - (s • D + G)) + principalCartierDivisor X u) ∧
            ∃ (g : X.functionFieldˣ) (z : X.presheaf.stalk x), z ≠ 0 ∧
              algebraMap (X.presheaf.stalk x) X.functionField z = (g : X.functionField) ∧
              M.IsLocalEquationAt x g ∧
              ((n * (s * d) * j : ℕ) : ℕ∞) < localAdicOrder (X.presheaf.stalk x) z := by
  obtain ⟨s, hs, G, hG, heff', hklt', hA⟩ :=
    original_klt_bpf_exists_small_effective_boundary_ample_adjoint K hdim hn hnorm ⟨J, hJ⟩
      cX fX d hd D heff hklt L a₀ hnef hbig
  let H := ((s * d) * a₀) • L - (s • D + G)
  have hνH : 1 ≤ cartierNumericalDimension K n hdim L H := by
    rw [← proper_nef_cartierNumericalDimension_ample_independent K n hdim hn L J H hL hJ hA]
    exact hν
  refine ⟨s, hs, G, hG, heff', hklt', hA, ?_⟩
  dsimp only
  let l := n.factorial * (n * (s * d) + 1) ^ n + 1
  have hconc := positive_numerical_nef_ample_pencil_exists_smoothLocus_effective_concentration
    K n hdim hn L H hL hA hνH (n * (s * d))
  change 1 ≤ l ∧ CartierIsAmpleProj K (l • L + H) ∧ _ at hconc
  obtain ⟨_, hample, j₀, hj₀, hcuts⟩ := hconc
  have heq : l • L + H = (l + (s * d) * a₀) • L - (s • D + G) := by
    dsimp [H]
    module
  refine ⟨heq ▸ hample, j₀, hj₀, ?_⟩
  intro j hj x hx hxsm
  obtain ⟨M, hM, ⟨u, hu⟩, g, z, hz, himage, hlocal, hord⟩ := hcuts j hj x hx hxsm
  refine ⟨M, hM, ⟨u, ?_⟩, g, z, hz, himage, hlocal, hord⟩
  change M = j • (l • L + H) + principalCartierDivisor X u at hu
  rwa [heq] at hu

end MixedFujita
