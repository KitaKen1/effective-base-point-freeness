/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.RoundupBoundaryNormalization

/-! The exceptional correction for a signed boundary depends only on its
fractional remainders. At most r+1 transverse components give a correction
between zero and r, exactly the projective vanishing interval. -/

@[expose] public section
open scoped BigOperators
namespace MixedFujita

noncomputable def blowupRoundupCorrection {ι : Type*} (s : Finset ι)
    (b : ι → ℤ) (d r : ℕ) : ℤ :=
  ⌈-((((∑ i ∈ s, b i) - (d : ℤ) * r : ℤ) : ℝ) / (d : ℝ))⌉ -
    ∑ i ∈ s, ⌈-((b i : ℝ) / (d : ℝ))⌉

theorem roundup_normalized_coefficient_eq_emod (b : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    b + (d : ℤ) * ⌈-((b : ℝ) / (d : ℝ))⌉ = b % (d : ℤ) := by
  obtain ⟨h0, h1⟩ := boundary_add_roundup_coefficient_mem_Ico b d hd
  calc
    b + (d : ℤ) * ⌈-((b : ℝ) / (d : ℝ))⌉ =
        (b + (d : ℤ) * ⌈-((b : ℝ) / (d : ℝ))⌉) % (d : ℤ) :=
      (Int.emod_eq_of_lt h0 h1).symm
    _ = _ := by rw [Int.add_mul_emod_self_left]

theorem blowupRoundupCorrection_eq_fractional {ι : Type*} (s : Finset ι)
    (b : ι → ℤ) (d r : ℕ) (hd : 1 ≤ d) :
    blowupRoundupCorrection s b d r =
      (r : ℤ) + ⌈-(((∑ i ∈ s, b i % (d : ℤ) : ℤ) : ℝ) / (d : ℝ))⌉ := by
  have hsum : ∑ i ∈ s, b i % (d : ℤ) =
      (∑ i ∈ s, b i) + (d : ℤ) * ∑ i ∈ s, ⌈-((b i : ℝ) / (d : ℝ))⌉ := by
    simp only [← roundup_normalized_coefficient_eq_emod _ d hd, Finset.sum_add_distrib,
      Finset.mul_sum]
  have hshift := boundary_roundup_add_integral_coefficient (∑ i ∈ s, b i) (-(r : ℤ)) d hd
  have hnorm := boundary_roundup_add_integral_coefficient (∑ i ∈ s, b i)
    (∑ i ∈ s, ⌈-((b i : ℝ) / (d : ℝ))⌉) d hd
  rw [hsum, hnorm]
  dsimp only [blowupRoundupCorrection]
  have heq : (∑ i ∈ s, b i) - (d : ℤ) * r = (∑ i ∈ s, b i) + (d : ℤ) * -(r : ℤ) := by ring
  rw [heq]
  rw [hshift]
  omega

theorem blowupRoundupCorrection_eq_floor {ι : Type*} (s : Finset ι)
    (b : ι → ℤ) (d r : ℕ) (hd : 1 ≤ d) :
    blowupRoundupCorrection s b d r =
      (r : ℤ) - ⌊((∑ i ∈ s, b i % (d : ℤ) : ℤ) : ℝ) / (d : ℝ)⌋ := by
  rw [blowupRoundupCorrection_eq_fractional s b d r hd, Int.ceil_neg]
  rfl

theorem blowupRoundupCorrection_mem_Icc {ι : Type*} (s : Finset ι)
    (b : ι → ℤ) (d r : ℕ) (hd : 1 ≤ d) (hs : s.card ≤ r + 1) :
    0 ≤ blowupRoundupCorrection s b d r ∧ blowupRoundupCorrection s b d r ≤ r := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h0 : 0 ≤ ∑ i ∈ s, b i % (d : ℤ) :=
    Finset.sum_nonneg (fun i _ => Int.emod_nonneg _ (ne_of_gt hdZ))
  have hbound : ∑ i ∈ s, b i % (d : ℤ) ≤ (s.card : ℤ) * ((d : ℤ) - 1) := by
    calc
      _ ≤ ∑ _i ∈ s, ((d : ℤ) - 1) := Finset.sum_le_sum (fun i _ => by
        have := Int.emod_lt_of_pos (b i) hdZ
        omega)
      _ = _ := by simp; ring
  have hsZ : (s.card : ℤ) ≤ r + 1 := by exact_mod_cast hs
  have hlt : ∑ i ∈ s, b i % (d : ℤ) < ((r : ℤ) + 1) * d := by
    nlinarith
  have hr0 : (0 : ℝ) ≤ ((∑ i ∈ s, b i % (d : ℤ) : ℤ) : ℝ) / (d : ℝ) :=
    div_nonneg (by exact_mod_cast h0) hdR.le
  have hrlt : ((∑ i ∈ s, b i % (d : ℤ) : ℤ) : ℝ) / (d : ℝ) < (r : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).mpr
    exact_mod_cast hlt
  have hf0 : 0 ≤ ⌊((∑ i ∈ s, b i % (d : ℤ) : ℤ) : ℝ) / (d : ℝ)⌋ := Int.floor_nonneg.mpr hr0
  have hfr : ⌊((∑ i ∈ s, b i % (d : ℤ) : ℤ) : ℝ) / (d : ℝ)⌋ ≤ (r : ℤ) :=
    (Int.floor_le_iff).mpr (by exact_mod_cast hrlt)
  rw [blowupRoundupCorrection_eq_floor s b d r hd]
  omega

end MixedFujita
