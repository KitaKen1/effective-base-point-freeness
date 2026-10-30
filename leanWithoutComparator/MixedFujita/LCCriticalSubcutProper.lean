/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCRoundupExceptionalCut

/-! 非零lc臨界切断から実roundup kernelの非有効性。 See reports/check-245-lc-kernel-closed-subscheme-lifting.json for the verified scope. The canonical lc kernel gives a proper nonzero actual image ideal, a concrete nonzero untwisted quotient unit, and a nonempty lower-dimensional actual closed subscheme W. Usual KV gives actual Cartier restriction section lifting to W. Usual KV itself and nonzero/generating sections of P restricted to W remain unproved; W is not identified with a reduced lc center; klt BPF and full F1/F2 remain incomplete. -/

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


/-- A nonzero coefficient-one critical cut makes its actual roundup kernel noneffective.
This supplies a missing global unit, without assuming properness of an abstract ideal. -/
theorem nonzero_lc_critical_roundup_subcut_not_effective
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (B E S : CartierDivisor T) (d : ℕ) (hd : 1 ≤ d) (hS : S.IsEffective) (hSne : S ≠ 0)
    (hSc : ∀ t : CodimensionOnePoint T, cartierCoefficient S (t : T) =
      if cartierCoefficient B (t : T) = (d : ℤ) then 1 else 0)
    (hround : ∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉) :
    ¬ (E - S).IsEffective := by
  obtain ⟨t, ht⟩ := exists_positive_prime_coefficient_of_effective_ne_zero hnormT S hS hSne
  have hBt : cartierCoefficient B (t : T) = (d : ℤ) := by
    by_contra hn
    rw [hSc, ite_eq_right hn] at ht
    omega
  intro hEff
  have hnon := cartierCoefficient_nonneg_of_isEffective _ hEff (t : T)
  rw [hround, hBt] at hnon
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  norm_num [hd0] at hnon

end MixedFujita
