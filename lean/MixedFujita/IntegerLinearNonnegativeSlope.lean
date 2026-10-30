/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Tactic

/-! 全自然数の整数一次評価から非負傾き。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
namespace MixedFujita
set_option maxHeartbeats 1600000

/-- A linear integer function nonnegative on every natural integer has
nonnegative slope, with an explicit finite contradiction if the slope is negative. -/
theorem int_nonneg_of_all_nat_mul_add_nonneg (x y : ℤ)
    (h : ∀ m : ℕ, 0 ≤ (m : ℤ) * x + y) : 0 ≤ x := by
  by_contra hx
  have hx' : x ≤ -1 := by omega
  have hy : y ≤ |y| := le_abs_self y
  have hm := h (y.natAbs + 1)
  have hmul := mul_le_mul_of_nonneg_left hx' (show (0 : ℤ) ≤ (y.natAbs + 1 : ℕ) by positivity)
  push_cast at hm hmul
  nlinarith only [hy, hm, hmul]

end MixedFujita
