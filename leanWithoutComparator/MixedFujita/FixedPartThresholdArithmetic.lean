/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteSNCThresholdArithmetic

/-! 固定部分閾値の全上限とN=a+1による可動係数制御。 See reports/check-248-high-power-lc-perturbation-complete-base.json for the verified scope. One high residual-power Bertini cut constructs an original effective lc non-klt perturbation klt outside the complete base locus, from one initial nonzero section and a nonempty base. SNC principalization, nonzero fixed part, residual generation, threshold, power and original section descent are internal. A nonempty reduced lower-dimensional non-klt W is internally placed inside that complete base locus without KV. Initial and restricted-section nonvanishing, automatic perturbed adjoint nef-big conditions, usual KV, klt BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
namespace MixedFujita
universe u
set_option maxHeartbeats 1600000

/-- Strict rational tests below a positive endpoint force each integer coefficient
to satisfy the non-strict endpoint bound. This needs no geometry or minimum witness. -/
theorem integer_perturbation_endpoint_le_of_strict_tests
    (b g : ℤ) (d a q : ℕ) (ha : 1 ≤ a) (hq : 1 ≤ q)
    (hbelow : ∀ p r : ℕ, 1 ≤ r → (p : ℚ) / r < (a : ℚ) / q →
      (r : ℤ) * b + ((d * p : ℕ) : ℤ) * g < ((r * d : ℕ) : ℤ)) :
    (q : ℤ) * b + ((d * a : ℕ) : ℤ) * g ≤ ((q * d : ℕ) : ℤ) := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((d : ℤ) * a * g)
  have hr : 1 ≤ (m + 1) * q := Nat.mul_pos (by omega) (by omega)
  have hratio : ((m * a : ℕ) : ℚ) / ((m + 1) * q : ℕ) < (a : ℚ) / q := by
    have haQ : (0 : ℚ) < a := by exact_mod_cast ha
    have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
    apply (div_lt_div_iff₀ (by exact_mod_cast hr) hqQ).mpr
    push_cast
    nlinarith [mul_pos haQ hqQ]
  have h := hbelow (m * a) ((m + 1) * q) hr hratio
  push_cast at h ⊢
  by_contra hn
  have hbad : (q : ℤ) * b + (d : ℤ) * a * g ≥ (q : ℤ) * d + 1 := by omega
  have hmul := mul_le_mul_of_nonneg_left hbad (by omega : (0 : ℤ) ≤ (m : ℤ) + 1)
  nlinarith


/-- The exact finite fixed-part threshold also gives ALL endpoint upper bounds.
The high-power choice N=a+1 makes every new moving coefficient strictly subcritical. -/
theorem finite_integer_fixed_part_threshold_with_subcritical_moving_power
    {r : ℕ} (b g : Fin r → ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hb : ∀ i, b i < (d : ℤ)) (hg : ∀ i, 0 ≤ g i) (hpos : ∃ i, 0 < g i) :
    ∃ a q : ℕ, 1 ≤ a ∧ 1 ≤ q ∧ a < q * (a + 1) ∧
      (∀ i, (q : ℤ) * b i + ((d * a : ℕ) : ℤ) * g i ≤ ((q * d : ℕ) : ℤ)) ∧
      (∃ i, 0 < g i ∧ (q : ℤ) * b i + ((d * a : ℕ) : ℤ) * g i = ((q * d : ℕ) : ℤ)) ∧
      ∀ i, (q : ℤ) * b i + ((d * a : ℕ) : ℤ) * g i = ((q * d : ℕ) : ℤ) → 0 < g i := by
  obtain ⟨a, q, i, ha, hq, hgi, _, heq, htest⟩ :=
    finite_integer_coefficients_exact_threshold b g d hd hb hg hpos
  have hsmall : a < q * (a + 1) := by nlinarith
  refine ⟨a, q, ha, hq, hsmall, ?_, ⟨i, hgi, heq⟩, ?_⟩
  · intro j
    exact integer_perturbation_endpoint_le_of_strict_tests (b j) (g j) d a q ha hq
      (fun p s hs hp => (htest p s hs).mpr hp j)
  · intro j hj
    have hj0 := hg j
    by_contra hn
    have hz : g j = 0 := by omega
    rw [hz, mul_zero, add_zero] at hj
    have hlt := mul_lt_mul_of_pos_left (hb j) (by omega : (0 : ℤ) < q)
    push_cast at hj
    omega

end MixedFujita
