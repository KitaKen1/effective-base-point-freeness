/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CenterPreservingBertiniParameters
public import MixedFujita.CartierSectionSNCPerturbation

/-! 先頭係数非零の大域残余SNC Bertini選択。 See reports/check-262-concentration-residual-snc.json for the verified scope. Actual natural global pullback is semilinear and linear over the actual base ring. SAME finite linear combinations preserve natural restriction, original nonvanishing and exact restricted concentration order. Actual fixed-part removal retains the rational function and recovers the original section. Given actual dominant principalization, the SAME original finite subsystem yields a residual basepointfree family; its linear combinations recover the original combinations with SAME coefficients. Existing global residual Bertini chooses first coefficient nonzero and an actual smooth reduced SNC cut with indicator coefficients. New model construction, final center-exterior LC coefficient bounds, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The existing GLOBAL residual Bertini polynomial can be met while keeping
the ORIGINAL fixed coefficient nonzero. This supplies actual reduced SNC
residual cuts in the SAME finite subsystem; no exterior open restriction is
needed. -/
theorem residual_finite_system_exists_first_nonzero_snc_parameter
    {K : Type u} [Field K] [CharZero K] [Infinite K]
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    (P : CartierDivisor T) (k : ℕ) (s : Fin (k + 1) → Γ(P.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree P s) {n r : ℕ} (ξ : Fin r → T)
    (hξ : IsSNCFamily K n ξ) :
    ∃ a : Fin (k + 1) → K, a 0 ≠ 0 ∧
      ∃ (ha : (∑ i, a i • s i) ≠ 0) (q : ℕ) (η : Fin q → T),
        Smooth (cartierSectionZeroSchemeι P (∑ i, a i • s i) ha ≫
          (T ↘ Spec (CommRingCat.of K))) ∧ Function.Injective η ∧
        (∀ j, Order.coheight (η j) = 1) ∧
        Set.range η = (cartierSectionZeroSchemeι P (∑ i, a i • s i) ha) ''
          genericPoints (cartierSectionZeroScheme P (∑ i, a i • s i) ha) ∧
        cartierSectionZeroLocus P (∑ i, a i • s i) = ⋃ j, closure ({η j} : Set T) ∧
        (Pairwise fun i j => Disjoint (closure ({η i} : Set T))
          (closure ({η j} : Set T))) ∧ IsSNCFamily K n (Fin.append ξ η) ∧
        (∀ x : CodimensionOnePoint T,
          cartierCoefficient (cartierSectionZeroDivisor P (∑ i, a i • s i) ha) (x : T) =
            if (x : T) ∈ Set.range η then 1 else 0) := by
  classical
  obtain ⟨p, hp, _, hgood⟩ := cartierSections_general_reduced_prime_snc P s hs ξ hξ
  obtain ⟨a, ha, ha0⟩ := exists_polynomial_good_parameter_with_first_coefficient_ne_zero k p hp
  exact ⟨a, ha0, hgood a ha⟩

end MixedFujita
