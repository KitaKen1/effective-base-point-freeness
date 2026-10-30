/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBasePrimeLocalLogCanonical
public import MixedFujita.BasePrimeGenerizations
public import MixedFujita.LogPairOverBasePoint

/-!
On a smooth SNC model, adding the actual Cartier pullback of a base-prime
uniformizer with coefficient one is log canonical over that prime on the
constructed transverse base open. The statement uses the original all-model
valuative predicate. Tests mapping to the prime use the joint adapted chart;
tests mapping to the generic point have zero extra order.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The coefficient-one actual base-prime pullback is all-model lc over that prime on the SNC model. -/
theorem snc_base_prime_pullback_logCanonical_overBasePoint
    {K : Type u} [Field K] [PerfectField K] {n : ℕ} {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (q : X ⟶ Y) [IsDominant q] (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) ≤ (d : ℤ))
    (V : Y.Opens) (htrans : SNCStrataUniformizerTransverseOn q (sncDivisorFamilyOfPoints ξ) V)
    (η : CodimensionOnePoint Y) (hηV : (η : Y) ∈ V)
    (H : CartierDivisor Y) (hH : H.IsEffective) (fH : Y.functionFieldˣ)
    (hfH : H.IsLocalEquationAt (η : Y) fH) (a : Y.presheaf.stalk (η : Y))
    (ha : algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField a = (fH : Y.functionField))
    (hairred : Irreducible a) :
    LogPairIsLogCanonicalOverBasePoint q (η : Y) c f d
      (d • (smoothCanonicalDivisor c + principalCartierDivisor X f) +
        (B + d • cartierPullback q H)) := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht hxη
  change (η : Y) ∈ closure ({q (ρ t)} : Set Y) at hxη
  rcases eq_or_eq_genericPoint_of_specializes_to_base_prime (η : Y) η.property (q (ρ t)) hxη with hy | hy
  · have hdata : ∃ f' : Y.functionFieldˣ, H.IsLocalEquationAt (q (ρ t)) f' ∧
        ∃ a' : Y.presheaf.stalk (q (ρ t)),
          algebraMap (Y.presheaf.stalk (q (ρ t))) Y.functionField a' = (f' : Y.functionField) ∧
          Irreducible a' := by
      rw [hy]
      exact ⟨fH, hfH, a, ha, hairred⟩
    obtain ⟨f', hf', a', ha', hairred'⟩ := hdata
    exact snc_base_prime_pullback_actual_logCanonical_bound_at_center
      q ρ hρ c f d B ξ hinj hξ hsnc hsupport cT ⟨t, ht⟩ (fun i _ => hb i)
      V htrans (by rw [hy]; exact hηV) (by rw [hy]; exact η.property)
      H hH f' hf' a' ha' hairred'
  · have hzero : cartierCoefficient (cartierPullback ρ (cartierPullback q H)) t = 0 := by
      have hz := cartierPullback_coefficient_eq_zero_of_image_genericPoint (ρ ≫ q) H hH t hy
      simpa only [cartierPullback_comp] using hz
    have hold := isSNCFamily_actual_logCanonical_bound_at_center ρ hρ c f d hd B ξ hinj hξ hsnc
      hsupport cT (⟨t, ht⟩ : CodimensionOnePoint T) (fun i _ => hb i)
    have hcoeff : cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d
        (d • (smoothCanonicalDivisor c + principalCartierDivisor X f) +
          (B + d • cartierPullback q H)) cT etaleCharts_cover) t =
        cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d
          (d • (smoothCanonicalDivisor c + principalCartierDivisor X f) + B)
          cT etaleCharts_cover) t - (d : ℤ) *
            cartierCoefficient (cartierPullback ρ (cartierPullback q H)) t := by
      unfold logDiscrepancyDivisor
      simp only [cartierPullback_add, cartierPullback_nsmul, cartierCoefficient_sub,
        cartierCoefficient_add, cartierCoefficient_nsmul]
      ring
    rw [hcoeff, hzero, mul_zero, sub_zero]
    exact hold

end MixedFujita
