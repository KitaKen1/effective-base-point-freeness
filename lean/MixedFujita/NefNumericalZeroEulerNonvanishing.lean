/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EulerPolynomialNonvanishing
public import MixedFujita.NefNumericalZeroSectionBounds
public import MixedFujita.NefNumericalZeroSectionRigidity
public import MixedFujita.CartierPrincipalFromSections
public import MixedFujita.PrincipalCartierGlobalGeneration

/-!
An Euler-polynomial shortcut in the numerical-zero branch of base point freeness.

Actual numerical dimension zero bounds every h⁰(mD) by one. If higher cohomology
vanishes eventually, the actual Euler polynomial is eventually {0,1}-valued,
hence constant. This avoids proving numerical invariance of Euler characteristic
via Riemann--Roch or Snapper as a separate prerequisite.

The remaining geometric inputs are explicit: eventual vanishing in ALL positive
cohomological degrees, and χ(O_X) ≠ 0. The existing H¹-only klt theorem does not
by itself supply these inputs in higher dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower

/-- Numerical dimension zero and eventual higher vanishing force the actual
Euler polynomial to be identically zero or identically one. -/
theorem proper_nef_numerical_zero_eulerPolynomial_eq_zero_or_one
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0)
    (hvan : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (m • D).sheaf (q + 1))) :
    cartierEulerPolynomial K n D 0 = 0 ∨ cartierEulerPolynomial K n D 0 = 1 := by
  apply rationalPolynomial_eq_zero_or_one_of_eventually_eval_nat
  obtain ⟨N, hN⟩ := hvan
  refine ⟨N, fun m hm => ?_⟩
  have h := proper_cartierEulerPolynomial_eval_int K n hdim.le D 0 (m : ℤ)
  simp only [natCast_zsmul, zero_add, Int.cast_natCast] at h
  rw [moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero K _ (hN m hm)] at h
  have hb := (proper_nef_numerical_zero_graded_sections_bound K n hdim hn D J hD hJ hzero m).2
  have hc : Module.finrank K Γ((m • D).sheaf, ⊤) = 0 ∨
      Module.finrank K Γ((m • D).sheaf, ⊤) = 1 := by omega
  rcases hc with hz | ho
  · left
    simpa only [hz, Int.natCast_zero, Int.cast_zero] using h
  · right
    simpa only [ho, Int.natCast_one, Int.cast_one] using h

/-- The zero-or-one alternative identifies the FULL Euler characteristic in
every signed degree with χ(O_X), using eventual vanishing and the section bound. -/
theorem proper_nef_numerical_zero_eulerChar_zsmul_eq
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0)
    (hvan : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (m • D).sheaf (q + 1))) (z : ℤ) :
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (z • D).sheaf =
      Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (0 : CartierDivisor X).sheaf := by
  have h := proper_nef_numerical_zero_eulerPolynomial_eq_zero_or_one
    K n hdim hn D J hD hJ hzero hvan
  have hz := proper_cartierEulerPolynomial_eval_int K n hdim.le D 0 z
  have h0 := proper_cartierEulerPolynomial_eval_int K n hdim.le D 0 0
  have heval : (cartierEulerPolynomial K n D 0).eval (z : ℚ) =
      (cartierEulerPolynomial K n D 0).eval 0 := by
    rcases h with h | h <;> rw [h] <;> simp
  have heq := hz.symm.trans (heval.trans h0)
  simp only [zero_add, zero_smul] at heq
  exact_mod_cast heq

/-- Under the two explicit cohomological inputs, an original nef numerical-zero
Cartier divisor is itself principal. Two consecutive large degrees remove the
possible torsion; in particular EVERY nonnegative multiple is globally generated. -/
theorem proper_nef_numerical_zero_principal_of_eventual_vanishing_of_euler_ne_zero
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0)
    (hvan : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (m • D).sheaf (q + 1)))
    (hχ : Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K))
      (0 : CartierDivisor X).sheaf ≠ 0) :
    (∃ f : X.functionFieldˣ, D = principalCartierDivisor X f) ∧
      ∀ m : ℕ, CartierIsGloballyGenerated (m • D) := by
  obtain ⟨N, hN⟩ := hvan
  have hprin (m : ℕ) (hm : max N 1 ≤ m) :
      ∃ f : X.functionFieldˣ, m • D = principalCartierDivisor X f := by
    have hχm : Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (m • D).sheaf ≠ 0 := by
      have heq := proper_nef_numerical_zero_eulerChar_zsmul_eq
        K n hdim hn D J hD hJ hzero ⟨N, hN⟩ (m : ℤ)
      simp only [natCast_zsmul] at heq
      rw [heq]
      exact hχ
    obtain ⟨s, hs⟩ := moduleSections_exists_nonzero_of_eulerChar_ne_zero K _ hχm
      (hN m ((le_max_left _ _).trans hm))
    have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < max N 1) hm
    exact (proper_nef_numerical_zero_section_seed_principal_multiple_and_numericallyTrivial
      K n hdim hn D J hD hJ hzero m hmpos s hs).1
  obtain ⟨f, hf⟩ := principal_of_consecutive_multiples D (max N 1)
    (hprin _ le_rfl) (hprin _ (by omega))
  refine ⟨⟨f, hf⟩, fun m => cartierIsGloballyGenerated_nsmul D ?_ m⟩
  rw [hf]
  exact principalCartierDivisor_globallyGenerated f

/-- If positive cohomology vanishes in EVERY nonnegative degree, including zero,
χ(O_X) is positive internally. Thus the numerical-zero branch needs no separately
supplied Euler invariant, nonzero section, or numerical-triviality dictionary. -/
theorem proper_nef_numerical_zero_principal_of_all_multiples_vanishing
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0)
    (hvan : ∀ m q : ℕ, q < n →
      Subsingleton (Scheme.Modules.Cohomology (m • D).sheaf (q + 1))) :
    (∃ f : X.functionFieldˣ, D = principalCartierDivisor X f) ∧
      ∀ m : ℕ, CartierIsGloballyGenerated (m • D) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hvanAll (m : ℕ) : ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (m • D).sheaf (q + 1)) :=
    positive_cohomology_subsingleton_of_finite_range _ n hdim.le (hvan m)
  apply proper_nef_numerical_zero_principal_of_eventual_vanishing_of_euler_ne_zero
    K n hdim hn D J hD hJ hzero ⟨0, fun m _ => hvanAll m⟩
  have hvan0 : ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (0 : CartierDivisor X).sheaf (q + 1)) := by
    simpa only [zero_nsmul] using hvanAll 0
  rw [moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero K _ hvan0]
  let := proper_cartier_sections_finite K (0 : CartierDivisor X)
  have hpos : 0 < Module.finrank K Γ((0 : CartierDivisor X).sheaf, ⊤) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      (cartierIsGloballyGenerated_exists_nonzero_section zeroCartierDivisor_globallyGenerated)
  exact ne_of_gt (Int.natCast_pos.mpr hpos)

end MixedFujita
