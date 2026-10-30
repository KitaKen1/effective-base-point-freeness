/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierPrincipalFromSections
public import MixedFujita.CartierNumericalTriviality
public import MixedFujita.ProperCurveOrderBounds
public import MixedFujita.PrincipalCartierGlobalGeneration

/-!
On a proper smooth integral curve over an algebraically closed field, a degree-zero Cartier
divisor has at most one independent section in every nonnegative degree. The existing geometric
degree/order estimate proves this without a Riemann--Roch or Iitaka-dimension premise.
Global generation therefore makes the divisor principal. One positive globally generated
multiple gives a principal positive multiple; eventual generation of all integer multiples
makes the divisor itself principal. The latter hypothesis is stronger than usual semiampleness.
Curve-test numerical triviality supplies degree zero by the identity curve map. These are curve
theorems, not a general-dimensional numerical-dimension-zero corollary.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
  [Smooth (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower

/-- Pullback along the identity has the actual intrinsic curve degree. -/
theorem cartierCurvePullbackDegree_id (hX : topologicalKrullDim X = 1)
    (D : CartierDivisor X) :
    cartierCurvePullbackDegree (K := K) D (𝟙 X) =
      properCurveCartierDegree (K := K) hX D :=
  cartierCurvePullbackDegree_eq_representation_degree (K := K) hX D (𝟙 X) D
    ((Scheme.Modules.pullbackId X).app D.sheaf)

/-- Numerical triviality supplies the intrinsic degree-zero condition, using the identity map. -/
theorem properSmoothCurve_degree_zero_of_numericallyTrivial (hX : topologicalKrullDim X = 1)
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D) :
    properCurveCartierDegree (K := K) hX D = 0 := by
  rw [← cartierCurvePullbackDegree_id (K := K) hX D]
  exact hD X hX (𝟙 X) (Category.id_comp _)

variable [IsAlgClosed K]

/-- Degree zero bounds every graded section space by one, using actual geometric order bounds. -/
theorem properSmoothCurve_graded_finrank_le_one_of_degree_zero
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hdeg : properCurveCartierDegree (K := K) hX D = 0) (j : ℕ) :
    Module.finrank K Γ((j • D).sheaf, ⊤) ≤ 1 := by
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton
    ⟨genericPoint X, Set.mem_univ _⟩
  simpa only [properCurveOrderBound, hdeg, Int.toNat_zero, mul_zero, zero_add] using
    properSmoothCurve_gradedSection_finrank_le_linearBound (K := K) hX D j x hx

/-- Global generation and intrinsic degree zero make the actual curve divisor principal. -/
theorem properSmoothCurve_principal_of_globallyGenerated_of_degree_zero
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hdeg : properCurveCartierDegree (K := K) hX D = 0)
    (hgg : CartierIsGloballyGenerated D) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  letI := properSmoothCurve_finiteDimensional_cartierSections (K := K) hX D
  apply principal_of_globallyGenerated_of_finrank_le_one (K := K) D hgg
  have h := properSmoothCurve_graded_finrank_le_one_of_degree_zero (K := K) hX D hdeg 1
  rw [show (1 : ℕ) • D = D from one_nsmul D] at h
  exact h

/-- Eventual generation of all integer multiples and degree zero make D itself principal. -/
theorem properSmoothCurve_principal_of_eventually_globallyGenerated_of_degree_zero
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hdeg : properCurveCartierDegree (K := K) hX D = 0)
    (hgg : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D)) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ :=
  principal_of_eventually_globallyGenerated_of_finrank_le_one (K := K) D hgg
    (properSmoothCurve_finiteDimensional_gradedSections (K := K) hX D)
    (properSmoothCurve_graded_finrank_le_one_of_degree_zero (K := K) hX D hdeg)

/-- A single positive globally generated multiple of a degree-zero divisor is principal.
This concludes torsion of the divisor class, rather than principality of D itself. -/
theorem properSmoothCurve_principal_multiple_of_degree_zero
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hdeg : properCurveCartierDegree (K := K) hX D = 0)
    (hgg : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    ∃ q : ℕ, 0 < q ∧ ∃ φ : X.functionFieldˣ, q • D = principalCartierDivisor X φ := by
  obtain ⟨q, hq, hgg⟩ := hgg
  refine ⟨q, hq, properSmoothCurve_principal_of_globallyGenerated_of_degree_zero
    (K := K) hX (q • D) ?_ hgg⟩
  rw [properCurveCartierDegree_nsmul, hdeg, mul_zero]

theorem properSmoothCurve_principal_of_globallyGenerated_of_numericallyTrivial
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : CartierIsNumericallyTrivial K D) (hgg : CartierIsGloballyGenerated D) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ :=
  properSmoothCurve_principal_of_globallyGenerated_of_degree_zero (K := K) hX D
    (properSmoothCurve_degree_zero_of_numericallyTrivial (K := K) hX D hD) hgg

theorem properSmoothCurve_principal_of_eventually_globallyGenerated_of_numericallyTrivial
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : CartierIsNumericallyTrivial K D)
    (hgg : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D)) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ :=
  properSmoothCurve_principal_of_eventually_globallyGenerated_of_degree_zero (K := K) hX D
    (properSmoothCurve_degree_zero_of_numericallyTrivial (K := K) hX D hD) hgg

theorem properSmoothCurve_principal_multiple_of_numericallyTrivial
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : CartierIsNumericallyTrivial K D)
    (hgg : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    ∃ q : ℕ, 0 < q ∧ ∃ φ : X.functionFieldˣ, q • D = principalCartierDivisor X φ :=
  properSmoothCurve_principal_multiple_of_degree_zero (K := K) hX D
    (properSmoothCurve_degree_zero_of_numericallyTrivial (K := K) hX D hD) hgg

/-- A degree-zero semiample curve divisor has actual Iitaka dimension zero: positive sections
occur on an unbounded arithmetic progression, and every graded section space has dimension at
most one. No Iitaka-dimension premise is supplied. -/
theorem properSmoothCurve_iitakaZero_of_degree_zero_of_positive_generated_multiple
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hdeg : properCurveCartierDegree (K := K) hX D = 0)
    (hgg : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    CartierIitakaDimension K D 0 := by
  obtain ⟨q, hq, hgg⟩ := hgg
  constructor
  · refine ⟨1, zero_lt_one, Filter.frequently_atTop.mpr ?_⟩
    intro b
    refine ⟨(b + 1) * q, by nlinarith, ?_⟩
    have hgen : CartierIsGloballyGenerated (((b + 1) * q) • D) := by
      rw [mul_nsmul']
      exact cartierIsGloballyGenerated_nsmul (q • D) hgg (b + 1)
    letI := properSmoothCurve_finiteDimensional_cartierSections (K := K) hX
      (((b + 1) * q) • D)
    have hpos : 0 < Module.finrank K Γ(((((b + 1) * q) • D)).sheaf, ⊤) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        (cartierIsGloballyGenerated_exists_nonzero_section hgen)
    have hle : (1 : ℝ) ≤ Module.finrank K Γ(((((b + 1) * q) • D)).sheaf, ⊤) := by
      exact_mod_cast hpos
    simpa only [pow_zero, mul_one] using hle
  · refine ⟨1, fun j => ?_⟩
    have hle := properSmoothCurve_graded_finrank_le_one_of_degree_zero (K := K) hX D hdeg j
    simp only [pow_zero, mul_one]
    exact_mod_cast hle

theorem properSmoothCurve_iitakaZero_of_numericallyTrivial_of_positive_generated_multiple
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : CartierIsNumericallyTrivial K D)
    (hgg : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    CartierIitakaDimension K D 0 :=
  properSmoothCurve_iitakaZero_of_degree_zero_of_positive_generated_multiple (K := K) hX D
    (properSmoothCurve_degree_zero_of_numericallyTrivial (K := K) hX D hD) hgg

/-- For numerically trivial divisors on these curves, global generation is equivalent to
linear triviality. -/
theorem properSmoothCurve_globallyGenerated_iff_principal_of_numericallyTrivial
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : CartierIsNumericallyTrivial K D) :
    CartierIsGloballyGenerated D ↔ ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  constructor
  · exact properSmoothCurve_principal_of_globallyGenerated_of_numericallyTrivial
      (K := K) hX D hD
  · rintro ⟨φ, rfl⟩
    exact principalCartierDivisor_globallyGenerated φ

end MixedFujita
