/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialNonvanishingSamples
public import MixedFujita.PulledModuleEulerPolynomial
public import MixedFujita.AmpleCartierHilbertPolynomial

/-!
Nonvanishing from the actual Euler polynomial, for the base point free theorem.

The coefficient can be any coherent module on a proper scheme, including a reduced
lc centre or an SNC cut. No ampleness of the Cartier direction is required.
The nonzero Euler value and the positive-cohomology vanishing are explicit inputs;
this module does not claim that the klt hypotheses already supply them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Nonzero Euler characteristic and actual higher-cohomology vanishing give an
actual nonzero global section, not merely a formal nonzero Hilbert value. -/
theorem moduleSections_exists_nonzero_of_eulerChar_ne_zero
    (K : Type u) [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
    (M : Y.Modules)
    (hχ : Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K)) M ≠ 0)
    (hvan : ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology M (q + 1))) :
    ∃ t : Γ(M, ⊤), t ≠ 0 := by
  classical
  by_contra! h
  let : Subsingleton Γ(M, ⊤) := ⟨fun a b => (h a).trans (h b).symm⟩
  apply hχ
  rw [moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero K M hvan,
    Module.finrank_zero_of_subsingleton, Int.natCast_zero]

/-- Only cohomological degrees `1, ..., n` need to be supplied. Degrees above
the geometric dimension vanish by the existing Grothendieck vanishing theorem. -/
theorem positive_cohomology_subsingleton_of_finite_range
    {Y : Scheme.{u}} [NoetherianSpace Y] (M : Y.Modules)
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n)
    (hvan : ∀ q : ℕ, q < n → Subsingleton (Scheme.Modules.Cohomology M (q + 1))) :
    ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology M (q + 1)) := by
  intro q
  by_cases hq : q < n
  · exact hvan q hq
  · apply actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt
    exact hdim.trans_lt (by exact_mod_cast (show n < q + 1 by omega))

/-- A nonzero Euler value at the untwisted coefficient makes its entire actual
Cartier Euler polynomial nonzero. -/
theorem proper_cartierPulledModuleEulerPolynomial_ne_zero
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (D E : CartierDivisor X)
    (hχ : Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor E p).obj M) ≠ 0) :
    cartierPulledModuleEulerPolynomial K p M n D E ≠ 0 := by
  intro hz
  have h := proper_cartierPulledModuleEulerPolynomial_eval_int K p M n hdim D E 0
  rw [hz] at h
  simp only [Polynomial.eval_zero, zero_smul, add_zero] at h
  exact hχ (by exact_mod_cast h.symm)

/-- Among any `n+1` distinct natural twists, one has a nonzero section if the
positive cohomology vanishes at those twists and the initial Euler value is nonzero.
The bound is geometric: `dim Y ≤ n`; no numerical-triviality dictionary is needed. -/
theorem proper_pulledEuler_exists_nonzero_section_sample
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (D E : CartierDivisor X)
    (hχ : Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor E p).obj M) ≠ 0)
    (s : Fin (n + 1) → ℕ) (hs : Function.Injective s)
    (hvan : ∀ i, ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology
      ((cartierPullbackTwistFunctor (E + s i • D) p).obj M) (q + 1))) :
    ∃ i, ∃ t : Γ((cartierPullbackTwistFunctor (E + s i • D) p).obj M, ⊤), t ≠ 0 := by
  obtain ⟨i, hi⟩ := rationalPolynomial_exists_nonzero_sample
    (cartierPulledModuleEulerPolynomial K p M n D E)
    (proper_cartierPulledModuleEulerPolynomial_ne_zero K p M n hdim D E hχ)
    n (cartierPulledModuleEulerPolynomial_natDegree_le K p M n D E) s hs
  refine ⟨i, moduleSections_exists_nonzero_of_eulerChar_ne_zero K _ ?_ (hvan i)⟩
  intro hz
  apply hi
  have h := proper_cartierPulledModuleEulerPolynomial_eval_int K p M n hdim D E (s i : ℤ)
  simpa only [Int.cast_natCast, natCast_zsmul, hz, Int.cast_zero] using h

/-- With eventual higher vanishing, the same nonzero Euler value yields sections
in every sufficiently large integer degree, rather than only in divisible degrees. -/
theorem proper_pulledEuler_eventually_exists_nonzero_section
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (D E : CartierDivisor X)
    (hχ : Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor E p).obj M) ≠ 0)
    (hvan : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology
        ((cartierPullbackTwistFunctor (E + m • D) p).obj M) (q + 1))) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ t : Γ((cartierPullbackTwistFunctor (E + m • D) p).obj M, ⊤), t ≠ 0 := by
  obtain ⟨N, hN⟩ := rationalPolynomial_eventually_eval_nat_ne_zero
    (cartierPulledModuleEulerPolynomial K p M n D E)
    (proper_cartierPulledModuleEulerPolynomial_ne_zero K p M n hdim D E hχ)
  obtain ⟨V, hV⟩ := hvan
  refine ⟨max N V, fun m hm => moduleSections_exists_nonzero_of_eulerChar_ne_zero K _ ?_
    (hV m ((le_max_right _ _).trans hm))⟩
  intro hz
  apply hN m ((le_max_left _ _).trans hm)
  have h := proper_cartierPulledModuleEulerPolynomial_eval_int K p M n hdim D E (m : ℤ)
  simpa only [Int.cast_natCast, natCast_zsmul, hz, Int.cast_zero] using h

/-- The finite window adapted to stable power base loci: for `b ≥ 2`, one of
the exponents `e, ..., e+n` supplies a nonzero section. Thus a stable base-locus
argument only needs higher vanishing at these finitely many powers. -/
theorem proper_pulledEuler_exists_nonzero_power_section
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (D E : CartierDivisor X)
    (hχ : Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor E p).obj M) ≠ 0)
    (b e : ℕ) (hb : 2 ≤ b)
    (hvan : ∀ f : ℕ, e ≤ f → f ≤ e + n → ∀ q : ℕ, q < n →
      Subsingleton (Scheme.Modules.Cohomology
        ((cartierPullbackTwistFunctor (E + (b ^ f) • D) p).obj M) (q + 1))) :
    ∃ f : ℕ, e ≤ f ∧ f ≤ e + n ∧
      ∃ t : Γ((cartierPullbackTwistFunctor (E + (b ^ f) • D) p).obj M, ⊤), t ≠ 0 := by
  let s : Fin (n + 1) → ℕ := fun i => b ^ (e + i.val)
  have hs : Function.Injective s := by
    intro i j hij
    apply Fin.ext
    have := Nat.pow_right_injective hb hij
    omega
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  obtain ⟨i, t, ht⟩ := proper_pulledEuler_exists_nonzero_section_sample
    K p M n hdim D E hχ s hs (fun i =>
      positive_cohomology_subsingleton_of_finite_range _ n hdim
        (hvan _ (by omega) (by have := i.isLt; omega)))
  exact ⟨e + i.val, by omega, by have := i.isLt; omega, t, ht⟩

end MixedFujita
