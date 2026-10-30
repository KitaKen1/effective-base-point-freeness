/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NormalBPFConcentration
public import MixedFujita.HighOrderNonLCPoint
public import MixedFujita.CartierLocalEquationLocus
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.GenericSmoothCharts

/-! 元正規BPFから任意開内の境界自由閉点と実有効非lc摂動。 See reports/check-253-singular-concentration-nonLC-point.json for the verified scope. Actual etale chart completions evaluate original global Cartier sections on a possibly singular integral source, without global smoothness. Original normal klt BPF data with positive numerical dimension construct all-high-power concentrated effective divisors at smooth closed points, without an initial L section or KV. Actual high regular-equation order obstructs the original all-model pointwise log-canonical and klt predicates. A boundary-free closed point in any nonempty open and effective non-lc perturbations are constructed internally. Initial and restricted nonvanishing, lc-threshold ample preservation, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- ORIGINAL normal klt BPF data with positive ORIGINAL numerical dimension
internally construct a boundary-free closed point in ANY nonempty open and actual
effective normalized concentration perturbations that are non-log-canonical over that point.
No initial L-section, KV, point, concentrated divisor or extraction is supplied. -/
theorem original_klt_BPF_positive_numerical_exists_effective_concentration_nonLC_point
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
    (hν : 1 ≤ cartierNumericalDimension K n hdim L J)
    (O : X.Opens) (hO : Nonempty O) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ G : CartierDivisor X, G.IsEffective ∧
      LogPairBoundaryEffective cX fX (s * d) (s • D + G) ∧
      LogPairIsKlt cX fX (s * d) (s • D + G) ∧
      CartierIsAmpleProj K (((s * d) * a₀) • L - (s • D + G)) ∧
      let l := n.factorial * (n * (s * d) + 1) ^ n + 1
      ∃ x : X, IsClosed {x} ∧ x ∈ O ∧ x ∈ cX.U ∧
        (s • D + G).IsLocalEquationAt x (fX ^ (s * d)) ∧
        ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j →
          ∃ M : CartierDivisor X, M.IsEffective ∧
            (∃ u : X.functionFieldˣ,
              M = j • ((l + (s * d) * a₀) • L - (s • D + G)) + principalCartierDivisor X u) ∧
            LogPairBoundaryEffective cX fX (j * (s * d)) (j • (s • D + G) + M) ∧
            ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) x cX fX (j * (s * d)) (j • (s • D + G) + M) := by
  obtain ⟨s, hs, G, hG, heff', hklt', hA, hample, j₀, hj₀, hcuts⟩ :=
    original_normal_klt_BPF_positive_numerical_constructs_normalized_concentration K n hdim hn hnorm
      cX fX d hd D heff hklt L hL a₀ hnef hbig J hJ hν
  obtain ⟨V, hV, hVne, _, hEq⟩ := exists_dense_open_localEquation
    (s • D + G) (fX ^ (s * d)) cX.U cX.nonempty
  let : Nonempty O := hO
  let : Nonempty V := hVne
  have hinter : ((O ⊓ V : X.Opens) : Set X).Nonempty :=
    ⟨genericPoint X, Scheme.genericPoint_mem O, Scheme.genericPoint_mem V⟩
  obtain ⟨x, hxcl, hxOV, hxsm⟩ := exists_closedPoint_mem_open_smoothLocus (K := K)
    ((O ⊓ V : X.Opens) : Set X) (O ⊓ V).isOpen hinter
  have hxc : x ∈ cX.U := hV hxOV.2
  have hDx := hEq x hxOV.2
  refine ⟨s, hs, G, hG, heff', hklt', hA, x, hxcl, hxOV.1, hxc, hDx, j₀, hj₀, ?_⟩
  intro j hj
  obtain ⟨M, hM, hlinear, g, z, hz, himage, hlocal, hord⟩ := hcuts j hj x hxcl hxsm
  have hjpos : 1 ≤ j := hj₀.trans hj
  have hsd : 1 ≤ s * d := by nlinarith
  have heffj := (logPairBoundaryEffective_scale_denominator_iff cX fX (s * d) j hjpos (s • D + G)).mpr heff'
  exact ⟨M, hM, hlinear,
    logPairBoundaryEffective_add_effective cX fX (j * (s * d)) _ M heffj hM,
    high_order_regular_equation_not_logCanonical_over_boundary_free_point hn cX fX (s * d) hsd
      (s • D + G) x hxc hxcl hDx j hjpos M g z hz himage hlocal hord⟩

end MixedFujita
