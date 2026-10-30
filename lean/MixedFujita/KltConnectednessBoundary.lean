/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformRoundupGeometry
public import MixedFujita.KltIsolationGeneration

/-!
The boundary of the connectedness argument for a klt pair (step 15, restriction to the fibres of
a product).

Let (c_X, f_X, d, D_X) be a pair on a normal variety X with effective boundary, ρ : T → X a proper
birational morphism from a smooth T, H and G effective Cartier divisors on T (the pullback of a
hypersurface and the divisor principalizing a family) and M ≥ 1. The boundary of the
connectedness argument for the pair (X, H + B + (1/M) 𝔞) is, with the denominator dM cleared,

  𝔅 = dM·H + M·B_crep + d·G,

where B_crep = ρ^*D_X − d·div(ρ^*ω) is the crepant boundary (`crepantBoundaryCartier`). Its
members of coefficient at least dM are the non-klt members. On prime divisors of T over prime
divisors of X the crepant boundary is d times the coefficient of the boundary, hence nonnegative
(`crepantBoundaryCartier_coefficient_nonneg_of_coheight`), so the positive part of the roundup
⌈−𝔅/(dM)⌉ is exceptional and has the canonical direct image isomorphism
(`exists_kltConnectedness_roundup_exceptional_pushforward`), as in the smooth case of check 349.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (DX : CartierDivisor X)
  (cT : EtaleChart K T n)

/-- For an effective boundary on a normal X whose codimension-one points lie in charts, the crepant
boundary is nonnegative at the prime divisors of a smooth model lying over prime divisors of X. -/
theorem crepantBoundaryCartier_coefficient_nonneg_of_coheight
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (heff : LogPairBoundaryEffective cX fX d DX) (z : CodimensionOnePoint T)
    (hz : Order.coheight (ρ (z : T)) = 1) :
    0 ≤ cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover) (z : T) := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hρ' : Function.Bijective (dominantFunctionFieldMap ρ).hom := hρ
  have hbij := stalkMap_bijective_of_birational_over_normal_prime hnormX ρ hρ' (z : T) hz
  let := hnormX (ρ (z : T))
  have : IsDiscreteValuationRing (X.presheaf.stalk (ρ (z : T))) :=
    normal_codimensionOne_stalk_DVR (⟨ρ (z : T), hz⟩ : CodimensionOnePoint X)
  have : IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) z
  obtain ⟨c', hc'⟩ := hcov (ρ (z : T)) hz
  rw [crepantBoundaryCartier_coefficient_of_stalkMap_bijective ρ hρ cX fX d DX cT z hz hbij c' hc']
  have h := heff c' (ρ (z : T)) hc' hz
  linarith

/-- The denominator-cleared boundary dM·H + M·B_crep + d·G of the connectedness argument for the
pair (X, H + B + (1/M) 𝔞). -/
noncomputable def kltConnectednessBoundary (H G : CartierDivisor T) (M : ℕ) : CartierDivisor T :=
  (d * M) • H + M • crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover + d • G

omit [IsLocallyNoetherian X] in
theorem kltConnectednessBoundary_coefficient (H G : CartierDivisor T) (M : ℕ) (t : T) :
    cartierCoefficient (kltConnectednessBoundary ρ hρ cX fX d DX cT H G M) t =
      ((d : ℤ) * M) * cartierCoefficient H t +
        (M : ℤ) * cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover) t +
        (d : ℤ) * cartierCoefficient G t := by
  simp only [kltConnectednessBoundary, cartierCoefficient_add, cartierCoefficient_nsmul]
  push_cast
  ring

omit [IsLocallyNoetherian X] in
/-- The boundary is supported on any family supporting H, the crepant boundary and G. -/
theorem kltConnectednessBoundary_supported (H G : CartierDivisor T) (M : ℕ) {r : ℕ}
    (ξ : Fin r → T)
    (hH : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient H (t : T) = 0)
    (hB : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient
      (crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover) (t : T) = 0)
    (hG : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) :
    ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (kltConnectednessBoundary ρ hρ cX fX d DX cT H G M) (t : T) = 0 := by
  intro t ht
  rw [kltConnectednessBoundary_coefficient, hH t ht, hB t ht, hG t ht]
  simp

/-- The boundary is nonnegative at the prime divisors of T over prime divisors of X. -/
theorem kltConnectednessBoundary_nonneg_over_prime
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (heff : LogPairBoundaryEffective cX fX d DX)
    (H G : CartierDivisor T) (hH : H.IsEffective) (hG : G.IsEffective) (M : ℕ)
    (t : CodimensionOnePoint T) (ht : Order.coheight (ρ (t : T)) = 1) :
    0 ≤ cartierCoefficient (kltConnectednessBoundary ρ hρ cX fX d DX cT H G M) (t : T) := by
  rw [kltConnectednessBoundary_coefficient]
  have h1 := cartierCoefficient_nonneg_of_isEffective H hH (t : T)
  have h2 := crepantBoundaryCartier_coefficient_nonneg_of_coheight ρ hρ cX fX d DX cT hnormX hcov
    heff t ht
  have h3 := cartierCoefficient_nonneg_of_isEffective G hG (t : T)
  positivity

/-- The exceptional part, the non-klt cut and the canonical direct image isomorphism of the
roundup ⌈−𝔅/(dM)⌉ on a smooth model of a normal X with an effective boundary. -/
theorem exists_kltConnectedness_roundup_exceptional_pushforward [IsProper ρ]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (heff : LogPairBoundaryEffective cX fX d DX) (hd : 1 ≤ d)
    (H G : CartierDivisor T) (hH : H.IsEffective) (hG : G.IsEffective)
    (M : ℕ) (hM : 1 ≤ M) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (kltConnectednessBoundary ρ hρ cX fX d DX cT H G M) (t : T) = 0) :
    ∃ (E S : CartierDivisor T) (hE : E.IsEffective) (_ : S.IsEffective),
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient (kltConnectednessBoundary ρ hρ cX fX d DX cT H G M)
          (t : T) : ℝ) / ((d * M : ℕ) : ℝ))⌉) ∧
      (∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) ↔
        ((d * M : ℕ) : ℤ) ≤ cartierCoefficient (kltConnectednessBoundary ρ hρ cX fX d DX cT H G M)
          (t : T)) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) = 0 ∨
        cartierCoefficient S (t : T) = 0) ∧
      (∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
        cartierCoefficient E (t : T) = 0) ∧
      IsIso (effectiveCartierPushforwardUnitMap ρ E hE) := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hdM : 1 ≤ d * M := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨E, S, hE, hS, hEc, hSc, hround, hdisj⟩ := exists_effective_snc_signed_roundup_split
    (kltConnectednessBoundary ρ hρ cX fX d DX cT H G M) (d * M) ξ hinj hξ hsnc hsupport
  have hexc (t : CodimensionOnePoint T) (ht : Order.coheight (ρ (t : T)) = 1) :
      cartierCoefficient E (t : T) = 0 := by
    rw [hEc]
    exact signed_roundup_exceptional_eq_zero _ (d * M) hdM
      (kltConnectednessBoundary_nonneg_over_prime ρ hρ cX fX d DX cT hnormX hcov heff H G hH hG M
        t ht)
  have hρ' : Function.Bijective (dominantFunctionFieldMap ρ).hom := hρ
  refine ⟨E, S, hE, hS, hround, fun t => ?_, hdisj, hexc,
    effectiveExceptionalCartierPushforwardUnitMap_isIso hnormX hnormT ρ hρ' E hE hexc⟩
  rw [hSc]
  exact signed_roundup_cut_positive_iff _ (d * M) hdM

end MixedFujita
