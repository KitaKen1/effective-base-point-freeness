/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ResidualBertiniFirstCoefficient
public import MixedFujita.CartierSectionBoundaryAvoidance

/-! 先頭非零かつ旧境界素成分を避ける同じ族のBertini。 See reports/check-263-exterior-lc-concentration.json for the verified scope. Actual SNC principalization of the SAME original finite subsystem and boundary-avoiding first-nonzero residual Bertini are assembled internally. Fixed-part coefficients vanish at EVERY prime relevant to points outside actual center support. Old LC coefficient bounds and new reduced-cut coefficients 0/1 prove original all-model pointwise exterior LC. Zero sections are filtered while preserving original nonzero indices. ALL high ample powers preserve nonzero natural restriction up to nonzero scalar and prove exterior LC. Positive RESTRICTED numerical dimension gives all-high actual concentrated original lifts preserving exact restricted order AND exterior LC. No original klt, normality, supplied model, initial L section or KV is required. Ambient nonLC from restricted concentration, actual lower-center iteration, original mL/center adjoint vanishing, nu=0, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Global residual Bertini with nonzero first coefficient can ALSO avoid every
old boundary generic point, making actual old/new prime supports disjoint. -/
theorem residual_first_nonzero_boundary_compatible_snc_parameter
    {K : Type u} [Field K] [CharZero K] [Infinite K]
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    (P : CartierDivisor T) (k : ℕ) (s : Fin (k + 1) → Γ(P.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree P s) {n r : ℕ} (ξ : Fin r → T)
    (hξ : IsSNCFamily K n ξ) :
    ∃ a : Fin (k + 1) → K, a 0 ≠ 0 ∧
      ∃ (ha : (∑ i, a i • s i) ≠ 0) (q : ℕ) (η : Fin q → T),
        Function.Injective η ∧ (∀ j, Order.coheight (η j) = 1) ∧
        IsSNCFamily K n (Fin.append ξ η) ∧ Disjoint (Set.range ξ) (Set.range η) ∧
        (∀ x : CodimensionOnePoint T,
          cartierCoefficient (cartierSectionZeroDivisor P (∑ i, a i • s i) ha) (x : T) =
            if (x : T) ∈ Set.range η then 1 else 0) := by
  classical
  obtain ⟨p, hp, _, hgood⟩ := cartierSections_general_reduced_prime_snc_avoiding
    P s hs ξ hξ (Set.range ξ) (Set.finite_range ξ)
  obtain ⟨a, ha, ha0⟩ := exists_polynomial_good_parameter_with_first_coefficient_ne_zero k p hp
  obtain ⟨hst, q, η, _, hinj, hη, hcover, hsnc, hcoeff, havoid⟩ := hgood a ha
  exact ⟨a, ha0, hst, q, η, hinj, hη, hsnc,
    cartierSection_component_ranges_disjoint P _ ξ η hcover (fun i => havoid _ ⟨i, rfl⟩), hcoeff⟩

end MixedFujita
