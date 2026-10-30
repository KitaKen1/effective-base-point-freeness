/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Max

/-!
The combinatorial threshold of the tie-breaking in the base point free theorem (step 16).

On a fixed SNC model let aᵢ < 1 be the boundary coefficients of a klt anchor, bᵢ ≤ 1 those of a
log canonical pair with bᵢ = 1 for at least one i, and gᵢ ≥ 0 the coefficients of an effective
correction. For every small ε = 1/M the coefficients
  cᵢ(s) = (1 − s) aᵢ + s bᵢ + ε gᵢ
of the interpolated and corrected boundary first reach 1 at some s = u/v ∈ [1/2, 1]; at that s
all cᵢ are at most 1, with equality exactly on a nonempty set J of indices with bᵢ = 1.
-/

@[expose] public section

namespace MixedFujita

/-- **Threshold with a small correction.** -/
theorem exists_rational_threshold_tie_break {ι : Type*} [Fintype ι] (a b g : ι → ℚ)
    (ha : ∀ i, a i < 1) (hb : ∀ i, b i ≤ 1) (hg : ∀ i, 0 ≤ g i) (hL : ∃ i, b i = 1) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∃ (u v : ℕ) (J : Finset ι), 1 ≤ u ∧ u ≤ v ∧ v ≤ 2 * u ∧ J.Nonempty ∧
        (∀ i ∈ J, b i = 1) ∧
        ∀ i, (1 - (u : ℚ) / v) * a i + ((u : ℚ) / v) * b i + g i / M ≤ 1 ∧
          ((1 - (u : ℚ) / v) * a i + ((u : ℚ) / v) * b i + g i / M = 1 ↔ i ∈ J) := by
  classical
  -- the size of M needed at each index
  let κ : ι → ℚ := fun i =>
    if b i = 1 then 2 * (g i + 1) / (1 - a i) else (g i + 1) / (1 - max (a i) (b i))
  have hκ : ∀ i, 0 ≤ κ i := by
    intro i
    simp only [κ]
    split_ifs with h
    · have : 0 < 1 - a i := by linarith [ha i]
      have : 0 ≤ g i + 1 := by linarith [hg i]
      positivity
    · have hmax : max (a i) (b i) < 1 := max_lt (ha i) (lt_of_le_of_ne (hb i) h)
      have : 0 < 1 - max (a i) (b i) := by linarith
      have : 0 ≤ g i + 1 := by linarith [hg i]
      positivity
  refine ⟨⌈∑ i, κ i⌉₊ + 1, fun M hM => ?_⟩
  have hMpos : (0 : ℚ) < M := by
    have : 1 ≤ M := le_trans (Nat.le_add_left 1 _) hM
    exact_mod_cast this
  have hMκ : ∀ i, κ i < M := by
    intro i
    have h1 : κ i ≤ ∑ j, κ j :=
      Finset.single_le_sum (fun j _ => hκ j) (Finset.mem_univ i)
    have h2 : ∑ j, κ j ≤ ⌈∑ j, κ j⌉₊ := Nat.le_ceil _
    have h3 : ((⌈∑ j, κ j⌉₊ + 1 : ℕ) : ℚ) ≤ M := by exact_mod_cast hM
    push_cast at h3
    linarith
  -- the lc indices and their thresholds
  let L : Finset ι := Finset.univ.filter (fun i => b i = 1)
  have hLne : L.Nonempty := by
    obtain ⟨i, hi⟩ := hL
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let σ : ι → ℚ := fun i => 1 - g i / M / (1 - a i)
  have hσ : ∀ i ∈ L, 1 / 2 ≤ σ i ∧ σ i ≤ 1 := by
    intro i hi
    have hbi : b i = 1 := (Finset.mem_filter.mp hi).2
    have h1a : 0 < 1 - a i := by linarith [ha i]
    have hκi := hMκ i
    simp only [κ, hbi, ite_true] at hκi
    have hgM : g i / M / (1 - a i) ≤ 1 / 2 := by
      rw [div_div, div_le_div_iff₀ (mul_pos hMpos h1a) (by norm_num)]
      rw [div_lt_iff₀ h1a] at hκi
      nlinarith [hg i]
    have hnn : 0 ≤ g i / M / (1 - a i) := by
      have := hg i
      positivity
    simp only [σ]
    constructor <;> linarith
  obtain ⟨i₁, hi₁L, hi₁min⟩ := L.exists_min_image σ hLne
  set s := σ i₁ with hs
  have hs12 : 1 / 2 ≤ s ∧ s ≤ 1 := hσ i₁ hi₁L
  -- u / v = s
  have hspos : 0 < s := by linarith [hs12.1]
  refine ⟨s.num.toNat, s.den, L.filter (fun i => σ i = s), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := Rat.num_pos.mpr hspos
    omega
  · have hle : s.num ≤ s.den := by
      have h1 : (s.num : ℚ) / s.den ≤ 1 := by rw [Rat.num_div_den]; exact hs12.2
      have hd : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
      rw [div_le_one hd] at h1
      exact_mod_cast h1
    have := Rat.num_pos.mpr hspos
    omega
  · have hle : (s.den : ℤ) ≤ 2 * s.num := by
      have h1 : (1 : ℚ) / 2 ≤ s.num / s.den := by rw [Rat.num_div_den]; exact hs12.1
      have hd : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
      rw [le_div_iff₀ hd] at h1
      have h2 : ((s.den : ℤ) : ℚ) ≤ 2 * (s.num : ℚ) := by push_cast; linarith
      exact_mod_cast h2
    have := Rat.num_pos.mpr hspos
    omega
  · exact ⟨i₁, Finset.mem_filter.mpr ⟨hi₁L, rfl⟩⟩
  · intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  · have hsuv : ((s.num.toNat : ℕ) : ℚ) / (s.den : ℕ) = s := by
      have := Rat.num_pos.mpr hspos
      have h : ((s.num.toNat : ℕ) : ℚ) = (s.num : ℚ) := by
        have : ((s.num.toNat : ℕ) : ℤ) = s.num := Int.toNat_of_nonneg this.le
        exact_mod_cast this
      rw [h]
      exact Rat.num_div_den s
    rw [hsuv]
    intro i
    by_cases hbi : b i = 1
    · have hiL : i ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hbi⟩
      have h1a : 0 < 1 - a i := by linarith [ha i]
      have hsi : s ≤ σ i := hi₁min i hiL
      have hrewrite : (1 - s) * a i + s * b i + g i / M =
          1 - (1 - a i) * (σ i - s) := by
        simp only [σ, hbi]
        field_simp
        ring
      rw [hrewrite]
      constructor
      · have : 0 ≤ (1 - a i) * (σ i - s) := mul_nonneg h1a.le (by linarith)
        linarith
      · constructor
        · intro h
          have h0 : (1 - a i) * (σ i - s) = 0 := by linarith
          have hσs : σ i = s := by
            rcases mul_eq_zero.mp h0 with h | h
            · exact absurd h h1a.ne'
            · linarith
          exact Finset.mem_filter.mpr ⟨hiL, hσs⟩
        · intro hiJ
          have hσs : σ i = s := (Finset.mem_filter.mp hiJ).2
          rw [hσs, sub_self, mul_zero, sub_zero]
    · have hmax : max (a i) (b i) < 1 := max_lt (ha i) (lt_of_le_of_ne (hb i) hbi)
      have hκi := hMκ i
      simp only [κ, hbi, ite_false] at hκi
      have h1m : 0 < 1 - max (a i) (b i) := by linarith
      have hgM : g i / M < 1 - max (a i) (b i) := by
        rw [div_lt_iff₀ hMpos]
        rw [div_lt_iff₀ h1m] at hκi
        nlinarith [hg i]
      have hconv : (1 - s) * a i + s * b i ≤ max (a i) (b i) := by
        have h1 : (1 - s) * a i ≤ (1 - s) * max (a i) (b i) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [hs12.2])
        have h2 : s * b i ≤ s * max (a i) (b i) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hspos.le
        nlinarith
      have hlt : (1 - s) * a i + s * b i + g i / M < 1 := by linarith
      refine ⟨hlt.le, ⟨fun h => absurd h hlt.ne, fun hiJ => ?_⟩⟩
      exact absurd (Finset.mem_filter.mp (Finset.mem_filter.mp hiJ).1).2 hbi

end MixedFujita
