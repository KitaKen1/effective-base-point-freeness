/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierPullbackTriviality
public import MixedFujita.SNCStrictTransformPrimes
public import MixedFujita.ReducedCartierSectionCoefficients

/-! An integral effective Cartier subscheme supplies its own codimension-one
generic point and, on a regular ambient scheme, its single-prime coefficient profile. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem integral_effectiveCartier_exists_prime
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (.of K))] (E : CartierDivisor X) (hE : E.IsEffective)
    (I : X.IdealSheafData) (hEI : effectiveCartierIdealSheaf E hE = I)
    [IsIntegral I.subscheme] :
    ∃ ξ : X, Order.coheight ξ = 1 ∧ IsGenericPoint ξ (I.support : Set X) := by
  obtain ⟨s, hs, heq, _⟩ := effectiveCartier_exists_canonical_section_with_exact_nonvanishing (K := K) E hE
  have hI : cartierSectionZeroIdeal E s hs = I := by
    change effectiveCartierIdealSheaf (cartierSectionZeroDivisor E s hs) _ = I
    simpa only [heq] using hEI
  let : IsIntegral (cartierSectionZeroScheme E s hs) := by
    change IsIntegral (cartierSectionZeroIdeal E s hs).subscheme
    rw [hI]
    infer_instance
  let η : genericPoints (cartierSectionZeroScheme E s hs) :=
    ⟨genericPoint _, by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _⟩
  refine ⟨cartierSectionZeroSchemeι E s hs η,
    cartierSectionZeroScheme_component_coheight_one (K := K) E s hs η, ?_⟩
  have h := (genericPoint_spec (cartierSectionZeroScheme E s hs)).image
    (cartierSectionZeroSchemeι E s hs).continuous
  rw [Set.image_univ] at h
  change IsGenericPoint (cartierSectionZeroSchemeι E s hs η)
    (closure (Set.range (cartierSectionZeroIdeal E s hs).subschemeι)) at h
  rw [Scheme.IdealSheafData.range_subschemeι, hI, I.support.isClosed.closure_eq] at h
  exact h

theorem integral_effectiveCartier_exists_primeProfile
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (.of K))] (E : CartierDivisor X) (hE : E.IsEffective)
    (I : X.IdealSheafData) (hEI : effectiveCartierIdealSheaf E hE = I)
    [IsIntegral I.subscheme]
    (hDVR : ∀ t : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (t : X))) :
    ∃ ξ : X, Order.coheight ξ = 1 ∧ IsGenericPoint ξ (I.support : Set X) ∧
      ∀ t : CodimensionOnePoint X, cartierCoefficient E (t : X) = if (t : X) = ξ then 1 else 0 := by
  obtain ⟨ξ, hcod, hgen⟩ := integral_effectiveCartier_exists_prime (K := K) E hE I hEI
  refine ⟨ξ, hcod, hgen, cartier_primeProfile_of_generic_support I E ξ hcod hgen ?_⟩
  obtain ⟨s, hs, heq, _⟩ := effectiveCartier_exists_canonical_section_with_exact_nonvanishing (K := K) E hE
  have hI : cartierSectionZeroIdeal E s hs = I := by
    change effectiveCartierIdealSheaf (cartierSectionZeroDivisor E s hs) _ = I
    simpa only [heq] using hEI
  let : IsReduced (cartierSectionZeroScheme E s hs) := by
    change IsReduced (cartierSectionZeroIdeal E s hs).subscheme
    rw [hI]
    infer_instance
  intro t
  let := hDVR t
  by_cases ht : (t : X) ∈ I.support
  · rw [ite_eq_left ht, ← heq]
    apply cartierSectionZeroDivisor_coefficient_one_of_reduced (K := K) E s hs t
    rw [← cartierSectionZeroIdeal_support (K := K) E s hs, hI]
    exact ht
  · rw [ite_eq_right ht]
    exact cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf E hE _
      (by rwa [hEI])

end MixedFujita
