/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialSubmoduleLocus
public import MixedFujita.DivisorialThresholdSubspace

/-!
Coefficient closedness for arbitrary finite-dimensional linear systems tested at fixed prime
divisors. Coefficients may depend polynomially on the parameters and cancellations are retained.
A fixed prime gives order subspaces with real thresholds rounded up exactly. Several specified
tests, even on different models, give a closed finite union. No exhaustiveness of a finite list
is claimed: the unrestricted existential realization locus still ranges over all test divisors.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
open scoped BigOperators

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Orders

variable {K : Type u} [Field K] {Y U : Scheme.{u}} [IsIntegral Y] [IsIntegral U]
  [Y.Over (Spec (CommRingCat.of K))] [U.Over (Spec (CommRingCat.of K))]
  (σ : U ⟶ Y) [σ.IsOver (Spec (CommRingCat.of K))]

omit [IsIntegral U] in
/-- Polynomial combinations of any finite section family satisfy simultaneous fixed-point
order lower bounds on a polynomial zero set. No bound on the span dimension is needed. -/
theorem exists_polynomialIdeal_sectionOrderConditions {τ : Type*} [Finite τ]
    (D : CartierDivisor Y) {N m : ℕ} (p : Fin N → U) (k : Fin N → ℕ)
    (b : Fin m → Γ(D.sheaf, ⊤)) (L : Fin N → Fin m → MvPolynomial τ K) :
    ∃ I : Ideal (MvPolynomial τ K),
      {c : τ → K | ∀ i, (k i : ℕ∞) ≤ cartierStalkPullbackOrder D σ (p i)
        (∑ j, MvPolynomial.eval c (L i j) • b j)} = polynomialZeroSet I := by
  classical
  let W : Fin N → Submodule K Γ(D.sheaf, ⊤) :=
    fun i => cartierStalkPullbackOrderAtLeast (K := K) σ D (p i) (k i)
  let I : Fin N → Ideal (MvPolynomial τ K) := fun i => submoduleMembershipIdeal (W i) b (L i)
  refine ⟨⨆ i, I i, ?_⟩
  ext c
  change (∀ i, (∑ j, MvPolynomial.eval c (L i j) • b j) ∈ W i) ↔ _
  rw [mem_polynomialZeroSet_iSup]
  exact forall_congr' fun i => (mem_polynomialZeroSet_submoduleMembershipIdeal (W i) b (L i) c).symm

end Orders

section Prime

variable {K : Type u} [Field K] {n : ℕ} {Y U : Scheme.{u}} [IsIntegral Y] [IsIntegral U]
  [Y.Over (Spec (CommRingCat.of K))] [U.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian U] [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- Actual coefficient closedness for realization by a specified prime divisor. The centre and
positive discrepancy conditions are retained; if either fails the locus is empty. -/
theorem exists_polynomialIdeal_primeTest {τ : Type*} [Finite τ]
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y)
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U) (x : Y) {N m : ℕ}
    (b : Fin m → Γ(D.sheaf, ⊤)) (L : Fin N → Fin m → MvPolynomial τ K) (α : Fin N → ℝ) :
    ∃ I : Ideal (MvPolynomial τ K),
      {c : τ → K | PrimeTestRealizesProfile σ hσ cY fY d D₀ D cU e x
        (fun i => ∑ j, MvPolynomial.eval c (L i j) • b j) α} = polynomialZeroSet I := by
  classical
  let A : ℝ := ((d : ℝ) + cartierCoefficient
    (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d
  by_cases hvalid : x ∈ closure ({σ (e : U)} : Set Y) ∧ 0 < A
  · obtain ⟨I, hI⟩ := exists_polynomialIdeal_sectionOrderConditions σ D
      (fun _ : Fin N => (e : U)) (fun i => ⌈α i * A⌉₊) b L
    refine ⟨I, ?_⟩
    rw [← hI]
    ext c
    simp only [Set.mem_ofPred_eq]
    rw [primeTestRealizesProfile_iff_orderSubspaces]
    change (x ∈ closure ({σ (e : U)} : Set Y) ∧ 0 < A ∧
      ∀ i, (⌈α i * A⌉₊ : ℕ∞) ≤ cartierStalkPullbackOrder D σ (e : U)
        (∑ j, MvPolynomial.eval c (L i j) • b j)) ↔ _
    simp only [hvalid.1, hvalid.2, true_and]
  · refine ⟨⊤, ?_⟩
    rw [polynomialZeroSet_top]
    ext c
    constructor
    · intro hc
      exact False.elim (hvalid ⟨hc.1, hc.2.1⟩)
    · exact False.elim

end Prime

section Finite

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- A finite list of fixed prime tests on possibly different smooth birational models has an
actual closed coefficient realization locus, for any finite section family. This is a finite
union theorem, not a reduction of unrestricted realization to finitely many fixed divisors. -/
theorem exists_polynomialIdeal_finitePrimeTests {ι τ : Type*} [Finite ι] [Finite τ]
    (U : ι → Scheme.{u}) [∀ j, IsIntegral (U j)] [∀ j, IsLocallyNoetherian (U j)]
    [∀ j, (U j).Over (Spec (CommRingCat.of K))]
    [∀ j, SmoothOfRelativeDimension n ((U j) ↘ Spec (CommRingCat.of K))]
    (σ : ∀ j, U j ⟶ Y) [∀ j, IsDominant (σ j)]
    [∀ j, (σ j).IsOver (Spec (CommRingCat.of K))]
    (hσ : ∀ j, Function.Bijective (dominantFunctionFieldAlgHom (K := K) (σ j)))
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y)
    (cU : ∀ j, EtaleChart K (U j) n) (e : ∀ j, CodimensionOnePoint (U j))
    (x : Y) {N m : ℕ} (b : Fin m → Γ(D.sheaf, ⊤))
    (L : Fin N → Fin m → MvPolynomial τ K) (α : Fin N → ℝ) :
    ∃ I : Ideal (MvPolynomial τ K),
      {c : τ → K | ∃ j, PrimeTestRealizesProfile (σ j) (hσ j) cY fY d D₀ D (cU j) (e j) x
        (fun i => ∑ k, MvPolynomial.eval c (L i k) • b k) α} = polynomialZeroSet I := by
  classical
  choose I hI using fun j => exists_polynomialIdeal_primeTest (σ j) (hσ j) cY fY d D₀ D
    (cU j) (e j) x b L α
  obtain ⟨J, hJ⟩ := exists_polynomialIdeal_finite_union I
  exact ⟨J, by simpa only [← hI, Set.ofPred_exists] using hJ⟩

end Finite

end MixedFujita
