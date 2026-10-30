/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic

/-!
Finite sampling for the nonvanishing step of the base point free theorem.
A nonzero degree-at-most-n polynomial cannot vanish at n+1 distinct degrees.
An eventually {0,1}-valued rational polynomial is identically zero or one.
-/

@[expose] public section

namespace MixedFujita

open Polynomial Filter

/-- Any `n+1` distinct natural degrees contain a nonroot. This includes consecutive
degrees, arithmetic progressions and powers of a fixed integer greater than one. -/
theorem rationalPolynomial_exists_nonzero_sample (P : ℚ[X]) (hP : P ≠ 0)
    (n : ℕ) (hdeg : P.natDegree ≤ n) (s : Fin (n + 1) → ℕ)
    (hs : Function.Injective s) :
    ∃ i, P.eval (s i : ℚ) ≠ 0 := by
  by_contra! h
  apply hP
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (fun i j hij => hs (Nat.cast_injective hij)) h (by simpa using hdeg)

/-- A nonzero polynomial is nonzero in every sufficiently large natural degree. -/
theorem rationalPolynomial_eventually_eval_nat_ne_zero (P : ℚ[X]) (hP : P ≠ 0) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → P.eval (m : ℚ) ≠ 0 := by
  obtain ⟨r, hr⟩ := P.exists_max_root hP
  obtain ⟨N, hN⟩ := exists_nat_gt r
  refine ⟨N, fun m hm hroot => ?_⟩
  exact (not_le_of_gt (hN.trans_le (by exact_mod_cast hm))) (hr _ hroot)

/-- Agreement in all sufficiently large integer degrees determines the whole polynomial,
including its value in degree zero. -/
theorem rationalPolynomial_eq_of_eventually_eval_nat_eq (P Q : ℚ[X])
    (h : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → P.eval (m : ℚ) = Q.eval (m : ℚ)) :
    P = Q := by
  obtain ⟨N, hN⟩ := h
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q
    (f := fun i : Fin (max P.natDegree Q.natDegree + 1) => ((N + i.val : ℕ) : ℚ))
  · intro i j hij
    apply Fin.ext
    have := Nat.cast_injective hij
    omega
  · intro i
    exact hN _ (by omega)
  · simp

/-- Eventual zero-or-one values force a constant polynomial. In the numerical-zero
branch these values come from the actual bound `h⁰(mD) ≤ 1`, after higher vanishing. -/
theorem rationalPolynomial_eq_zero_or_one_of_eventually_eval_nat
    (P : ℚ[X])
    (h : ∃ N : ℕ, ∀ m : ℕ, N ≤ m → P.eval (m : ℚ) = 0 ∨ P.eval (m : ℚ) = 1) :
    P = 0 ∨ P = 1 := by
  have hprod : P * (P - 1) = 0 := by
    apply rationalPolynomial_eq_of_eventually_eval_nat_eq
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun m hm => ?_⟩
    rcases hN m hm with hz | ho
    · simp [hz]
    · simp [ho]
  simpa only [sub_eq_zero] using mul_eq_zero.mp hprod

end MixedFujita
