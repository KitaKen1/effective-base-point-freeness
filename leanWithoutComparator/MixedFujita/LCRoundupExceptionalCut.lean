/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCLCRoundupSplit
public import MixedFujita.KltRoundupExceptional
public import MixedFujita.CrepantSNCBasePointLogCanonical
public import MixedFujita.NormalCartierEffectivity
public import MixedFujita.NormalEffectiveCartierPrime

/-! 元lc対の有効例外roundupと臨界切断・摂動引き戻し内の位置。 See reports/check-244-lc-critical-cut-roundup-kernel.json for the verified scope. Actual lc critical Cartier cuts and effective exceptional roundup parts are constructed. An original projective effective lc non-klt pair yields an internal smooth projective model, nonempty cut, coherent embedded kernel and usual-KV-based H1 vanishing and quotient section lifting. Usual KV and cut-generator existence remain unproved; the kernel is not identified with a reduced lc-center ideal; klt BPF and full F1/F2 remain incomplete. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- On an actual SNC model of an ORIGINAL effective lc pair, construct the positive
exceptional roundup part and the coefficient-one critical Cartier cut. The cut is zero
exactly when the ORIGINAL pair is klt; no cut or exceptional divisor is input. -/
theorem exists_effective_exceptional_lc_boundary_roundup_split
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))] [IsProper p]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hlc : LogPairIsLogCanonical cX fX d D) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover) (t : T) = 0) :
    ∃ (E S : CartierDivisor T), E.IsEffective ∧ S.IsEffective ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient S (t : T) =
        if cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover)
          (t : T) = (d : ℤ) then 1 else 0) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      (∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 →
        cartierCoefficient E (t : T) = 0) ∧
      (S = 0 ↔ LogPairIsKlt cX fX d D) := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  let B := crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover
  have hb (t : CodimensionOnePoint T) : cartierCoefficient B (t : T) ≤ (d : ℤ) :=
    logPairIsLogCanonical_crepantBoundary_coefficient_le p hp cX fX d D hlc cT t
  obtain ⟨E, S, hE, hS, hSc, hEc, hround⟩ := exists_effective_snc_lc_roundup_split
    B d hd ξ hinj hξ hsnc hsupport (fun i => hb ⟨ξ i, hξ i⟩)
  refine ⟨E, S, hE, hS, hSc, hround, fun t ht => ?_, ?_⟩
  · rw [hEc t, hSc t]
    exact lc_roundup_positive_part_eq_zero _ d hd
      (crepantBoundary_coefficient_nonneg_over_normal_prime p hp hnorm hcov cX fX d D heff cT t ht)
      (hb t)
  · exact (snc_lc_critical_cut_eq_zero_iff_strict hnormT B S d hd ξ hξ hsupport
      (fun i => hb ⟨ξ i, hξ i⟩) hSc).trans
      (logPairIsKlt_iff_crepant_snc_coefficients p hp cX fX d hd D cT ξ hinj hξ hsnc hsupport).symm


/-- For a rational effective perturbation of an ORIGINAL klt pair, every critical
coefficient-one component uses a positive coefficient of the ACTUAL perturbing pullback.
Thus the actual critical cut is bounded by that effective pullback as Cartier divisors. -/
theorem critical_lc_cut_le_effective_klt_perturbation_pullback
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))] [IsProper p]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor X) (hklt : LogPairIsKlt cX fX d D)
    (G : CartierDivisor X) (hG : G.IsEffective) (a q : ℕ) (hq : 1 ≤ q)
    (cT : EtaleChart K T n) (S : CartierDivisor T)
    (hSc : ∀ t : CodimensionOnePoint T, cartierCoefficient S (t : T) =
      if cartierCoefficient (crepantBoundaryCartier p hp cX fX (q * d)
        (q • D + (d * a) • G) cT etaleCharts_cover) (t : T) = ((q * d : ℕ) : ℤ) then 1 else 0) :
    (cartierPullback p G - S).IsEffective := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  apply (normal_cartier_isEffective_iff_coefficients_nonneg hnormT _).mpr
  intro t
  rw [cartierCoefficient_sub, hSc t]
  have hnon := cartierCoefficient_nonneg_of_isEffective _
    (cartierPullback_effective_of_effective p G hG) (t : T)
  split_ifs with hcrit
  · have hpos : 0 < cartierCoefficient (cartierPullback p G) (t : T) := by
      by_contra hnot
      have hz : cartierCoefficient (cartierPullback p G) (t : T) = 0 := by omega
      rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
        cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul,
        cartierCoefficient_nsmul, hz, mul_zero, add_zero, Nat.cast_mul] at hcrit
      have hb := logPairIsKlt_crepantBoundary_coefficient_lt p hp cX fX d D hklt cT t
      have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
      nlinarith
    omega
  · omega

end MixedFujita
