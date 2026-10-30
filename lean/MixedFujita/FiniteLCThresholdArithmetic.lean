/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteSNCThresholdArithmetic

/-! 旧臨界係数を除く有限整数lc閾値の正の厳密有理最小値。 See reports/check-257-lc-threshold-subcenter-descent.json for the verified scope. Original lc pairs with a nonzero effective divisor avoiding all old actual lc centers have an internally constructed exact positive rational threshold and a new actual lc center. Discrepancy convexity confines a new center to the prescribed closed set if a larger coefficient is lc outside it. An actual non-lc point, old-center avoidance and exterior lc imply a strict new subcenter. Canonical reduced strict subcenters have strictly smaller ordinary Krull dimension, using an internally constructed closed immersion. These are conditional criteria: the Bertini divisor and actual ambient non-lc point from restricted concentration are not yet constructed. Center normality, center classification, general KV, original L nonvanishing and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
namespace MixedFujita
set_option maxHeartbeats 600000

/-- An lc coefficient family has a POSITIVE exact rational threshold when its
critical old coefficients have zero perturbation coefficient. Only the positive
perturbation coordinates enter the finite minimum; old critical ones persist. -/
theorem finite_integer_lc_coefficients_exact_threshold
    {r : ℕ} (b g : Fin r → ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hb : ∀ i, b i ≤ (d : ℤ)) (hg : ∀ i, 0 ≤ g i)
    (hcritical : ∀ i, b i = (d : ℤ) → g i = 0) (hpos : ∃ i, 0 < g i) :
    ∃ (a q₀ : ℕ) (i₀ : Fin r), 1 ≤ a ∧ 1 ≤ q₀ ∧ 0 < g i₀ ∧ b i₀ < (d : ℤ) ∧
      (a : ℚ) / (q₀ : ℚ) = ((d : ℚ) - b i₀) / ((d : ℚ) * g i₀) ∧
      (q₀ : ℤ) * b i₀ + ((d * a : ℕ) : ℤ) * g i₀ = ((q₀ * d : ℕ) : ℤ) ∧
      ∀ (p q : ℕ), 1 ≤ q →
        ((∀ i, (q : ℤ) * b i + ((d * p : ℕ) : ℤ) * g i ≤ ((q * d : ℕ) : ℤ)) ↔
          (p : ℚ) / (q : ℚ) ≤ (a : ℚ) / (q₀ : ℚ)) := by
  classical
  let I := {i : Fin r // 0 < g i}
  let : Nonempty I := by obtain ⟨i, hi⟩ := hpos; exact ⟨⟨i, hi⟩⟩
  obtain ⟨i₀, hmin⟩ := Finite.exists_min
    (fun i : I => ((d : ℚ) - b i.1) / ((d : ℚ) * g i.1))
  have hstrict : b i₀.1 < (d : ℤ) := by
    have h := hb i₀.1
    have hc := hcritical i₀.1
    have hp := i₀.property
    omega
  let a := ((d : ℤ) - b i₀.1).toNat
  let q₀ := d * (g i₀.1).toNat
  have hgap : 0 < (d : ℤ) - b i₀.1 := sub_pos.mpr hstrict
  have haZ : (a : ℤ) = (d : ℤ) - b i₀.1 := Int.toNat_of_nonneg hgap.le
  have hgZ : ((g i₀.1).toNat : ℤ) = g i₀.1 := Int.toNat_of_nonneg i₀.property.le
  have ha : 1 ≤ a := by omega
  have hgn : 0 < (g i₀.1).toNat := by have := i₀.property; omega
  have hq₀ : 1 ≤ q₀ := Nat.mul_pos (by omega) hgn
  have hqZ : (q₀ : ℤ) = (d : ℤ) * g i₀.1 := by dsimp [q₀]; rw [hgZ]
  have haQ : (a : ℚ) = (d : ℚ) - b i₀.1 := by exact_mod_cast haZ
  have hqQ : (q₀ : ℚ) = (d : ℚ) * g i₀.1 := by exact_mod_cast hqZ
  have hratio : (a : ℚ) / q₀ = ((d : ℚ) - b i₀.1) / ((d : ℚ) * g i₀.1) := by rw [haQ, hqQ]
  refine ⟨a, q₀, i₀.1, ha, hq₀, i₀.property, hstrict, hratio, ?_, ?_⟩
  · simp only [q₀, Nat.cast_mul, haZ, hgZ]
    ring
  · intro p q hq
    constructor
    · intro h
      rw [hratio]
      exact (integer_perturbation_coefficient_le_iff (b i₀.1) (g i₀.1) d p q hd hq i₀.property).mp (h i₀.1)
    · intro h i
      by_cases hgi : 0 < g i
      · apply (integer_perturbation_coefficient_le_iff (b i) (g i) d p q hd hq hgi).mpr
        rw [hratio] at h
        exact h.trans (hmin ⟨i, hgi⟩)
      · have hzero : g i = 0 := by have := hg i; omega
        have hmul := mul_le_mul_of_nonneg_left (hb i) (by exact_mod_cast Nat.zero_le q : (0 : ℤ) ≤ q)
        simpa only [hzero, mul_zero, add_zero, Nat.cast_mul] using hmul

end MixedFujita
