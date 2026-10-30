/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.RationalThresholdLogCanonical

/-! 元全モデルlog canonical条件の正分母スケール不変性。 See reports/check-254-positive-numerical-lc-ample-source.json for the verified scope. Actual non-lc concentration internally gives a strictly smaller rational effective lc non-klt endpoint. Actual Cartier decomposition preserves an ample original L-adjoint in every large degree. Original normal klt BPF data with positive original numerical dimension construct a canonical nonempty reduced lower-dimensional non-klt source without an initial L section or KV; codimension-one charts follow internally from normality. The same source has all-large-original-L restriction lifting under explicit usual H1 KV. Initial and positive-dimensional restricted nonvanishing, minimal lc-center geometry, center-exterior control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Positive denominator scaling preserves the ORIGINAL all-model log-canonical
predicate, by actual discrepancy scaling and positive integer cancellation. -/
theorem logPairIsLogCanonical_scale_denominator_iff
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d m : ℕ) (hm : 1 ≤ m)
    (D : CartierDivisor X) :
    LogPairIsLogCanonical c f (m * d) (m • D) ↔ LogPairIsLogCanonical c f d D := by
  have hmpos : (0 : ℤ) < m := by exact_mod_cast hm
  have hscale (a : ℤ) : -((m * d : ℕ) : ℤ) ≤ (m : ℤ) * a ↔ -(d : ℤ) ≤ a := by
    rw [Nat.cast_mul, neg_mul_eq_mul_neg, mul_le_mul_iff_of_pos_left hmpos]
  constructor
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht
    have hb := h T ρ hρ cT t ht
    rw [logDiscrepancyDivisor_scale_denominator, cartierCoefficient_nsmul, hscale] at hb
    exact hb
  · intro h T _ _ _ _ ρ _ _ _ hρ cT t ht
    rw [logDiscrepancyDivisor_scale_denominator, cartierCoefficient_nsmul, hscale]
    exact h T ρ hρ cT t ht

end MixedFujita
