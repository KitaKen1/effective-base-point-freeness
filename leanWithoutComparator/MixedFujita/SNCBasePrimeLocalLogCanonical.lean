/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCCartierCutLogCanonical

/-! The actual base-prime Cartier pullback supplies its own adapted equation
chart and satisfies the coefficient-one discrepancy bound at any test prime
whose centre maps to that base prime. No chart or source equation is input. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- All actual birational tests with centre over a base prime satisfy the coefficient-one lc bound. -/
theorem snc_base_prime_pullback_actual_logCanonical_bound_at_center
    {K : Type u} [Field K] [PerfectField K] {n : ℕ} {X T Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T] [IsLocallyNoetherian Y]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (q : X ⟶ Y) [IsDominant q] (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T)
    (hb : ∀ i, ρ (t : T) ∈ closure ({ξ i} : Set X) → cartierCoefficient B (ξ i) ≤ (d : ℤ))
    (V : Y.Opens) (htrans : SNCStrataUniformizerTransverseOn q (sncDivisorFamilyOfPoints ξ) V)
    (hxV : q (ρ (t : T)) ∈ V) (hcoh : Order.coheight (q (ρ (t : T))) = 1)
    (H : CartierDivisor Y) (hH : H.IsEffective) (fH : Y.functionFieldˣ)
    (hfH : H.IsLocalEquationAt (q (ρ (t : T))) fH) (a : Y.presheaf.stalk (q (ρ (t : T))))
    (ha : algebraMap (Y.presheaf.stalk (q (ρ (t : T)))) Y.functionField a = (fH : Y.functionField))
    (hairred : Irreducible a) :
    -(d : ℤ) ≤ cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
        (B + d • cartierPullback q H)) cT etaleCharts_cover) (t : T) := by
  letI : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨c, σ, j, hc, hchart, hEq⟩ :=
    exists_sncChartWith_localEquation_cartierPullback_of_base_uniformizer
      q ξ hsnc V htrans (ρ (t : T)) hxV hcoh H hH fH hfH a ha hairred
  exact isSNCChartWith_actual_logCanonical_bound_with_cut_at_center ρ hρ c₀ f₀ d B
    (cartierPullback q H) ξ hinj hξ hsnc hsupport cT t hb c σ _ j hc hchart hEq

end MixedFujita
