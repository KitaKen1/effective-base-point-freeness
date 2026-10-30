/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SliceRestrictionCount
public import MixedFujita.JacobianValuationBound
public import Mathlib.Data.Finsupp.Interval

/-!
Restriction to the tangent directions in coordinates. Let ψ : K[[x, τ]] → K[[τ]] be a K-algebra
map with ψ(x_i) = 0 and ψ(τ_t) = τ_t, such as the map of completed local rings of the closed
immersion of W at a point where W = {x = 0} in the coordinates (x, τ). In characteristic zero
ψ does not lower the order (Euler's identity, for maps between different power series rings), so
the coefficients of ψ F of total degree N depend only on the truncation of F in degree N, where
ψ acts on monomials by killing every monomial in x. Hence the coefficient of ψ F at β is the
coefficient of F at (0, β). For the restriction image R = ψ ∘ T and positive weights on all
normal directions, the hypotheses of the count #G_0(h) ≥ I_W(h) of §5.2 hold: there are no
exponents of zero old weight with a nonzero normal part.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries Finset

variable {K : Type*} [Field K]

/-- A K-algebra map between power series rings sending the variables into the maximal ideal
does not lower the order. -/
theorem le_order_algHom_of_le_order [CharZero K] {σ τ : Type*} [Fintype σ]
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries τ K)
    (hψ : ∀ i, constantCoeff (ψ (X i)) = 0) :
    ∀ (k : ℕ) (G : MvPowerSeries σ K), (k : ℕ∞) ≤ G.order → (k : ℕ∞) ≤ (ψ G).order := by
  intro k
  induction k with
  | zero =>
    intro G _
    simp
  | succ k ih =>
    intro G hG
    have hc : constantCoeff G = 0 := by
      rw [← one_le_order_iff_constCoeff_eq_zero]
      exact le_trans (by exact_mod_cast Nat.succ_pos k) hG
    obtain ⟨G', hG'ord, hG'eq⟩ := exists_euler_preimage hc
    rw [hG'eq, map_sum]
    apply le_weightedOrder_sum (fun _ => 1)
    intro i _
    rw [map_mul]
    have hX : (1 : ℕ∞) ≤ (ψ (X i)).order := one_le_order_iff_constCoeff_eq_zero.mpr (hψ i)
    have hd : (k : ℕ∞) ≤ (pderiv i G').order :=
      enat_le_of_succ_le_add_one ((hG.trans hG'ord).trans (order_le_pderiv_add_one i G'))
    have hk := ih _ hd
    calc ((k + 1 : ℕ) : ℕ∞) = 1 + k := by push_cast; ring
      _ ≤ (ψ (X i)).order + (ψ (pderiv i G')).order := add_le_add hX hk
      _ ≤ (ψ (X i) * ψ (pderiv i G')).order := le_order_mul

section Restriction

variable {ρ τ : Type*}

theorem sumElim_add_sumElim (a a' : ρ →₀ ℕ) (b b' : τ →₀ ℕ) :
    Finsupp.sumElim a b + Finsupp.sumElim a' b' = Finsupp.sumElim (a + a') (b + b') := by
  ext (i | i) <;> rfl

variable (ψ : MvPowerSeries (ρ ⊕ τ) K →ₐ[K] MvPowerSeries τ K)

/-- ψ fixes the tangent monomials. -/
theorem algHom_monomial_tangent (hτ : ∀ t, ψ (X (Sum.inr t)) = X t) (b : τ →₀ ℕ) :
    ψ (monomial (Finsupp.sumElim 0 b) 1) = monomial b 1 := by
  induction b using Finsupp.induction_linear with
  | zero => rw [Finsupp.sumElim_zero_zero, monomial_zero_one, map_one, monomial_zero_one]
  | add f g hf hg =>
    rw [← add_zero (0 : ρ →₀ ℕ), ← sumElim_add_sumElim, ← mul_one (1 : K),
      ← monomial_mul_monomial, map_mul, hf, hg, monomial_mul_monomial, mul_one]
  | single t k =>
    classical
    rw [Finsupp.sumElim_zero_single, ← X_pow_eq, map_pow, hτ, X_pow_eq]

/-- ψ kills every monomial in the normal variables. -/
theorem algHom_monomial_normal (hρ : ∀ i, ψ (X (Sum.inl i)) = 0) {a : ρ →₀ ℕ} (ha : a ≠ 0)
    (b : τ →₀ ℕ) : ψ (monomial (Finsupp.sumElim a b) 1) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (Finsupp.ext h)
  have hsplit : Finsupp.sumElim a b =
      Finsupp.single (Sum.inl i) 1 + Finsupp.sumElim (a - Finsupp.single i 1) b := by
    ext (j | j)
    · simp only [Finsupp.add_apply, Finsupp.sumElim_inl, Finsupp.tsub_apply,
        Finsupp.single_apply, Sum.inl.injEq]
      by_cases hji : i = j
      · subst hji
        simp only [ite_true]
        omega
      · simp only [hji, ite_false, zero_add, tsub_zero]
    · simp only [Finsupp.add_apply, Finsupp.sumElim_inr, Finsupp.single_apply,
        reduceCtorEq, ite_false, zero_add]
  rw [hsplit, ← mul_one (1 : K), ← monomial_mul_monomial, map_mul, ← X_def, hρ, zero_mul]

/-- The coefficient of the image of a monomial. -/
theorem coeff_algHom_monomial [Fintype ρ] [Fintype τ] [DecidableEq ρ] [DecidableEq τ]
    (hρ : ∀ i, ψ (X (Sum.inl i)) = 0)
    (hτ : ∀ t, ψ (X (Sum.inr t)) = X t) (e : (ρ ⊕ τ) →₀ ℕ) (c : K) (β : τ →₀ ℕ) :
    coeff β (ψ (monomial e c)) = if e = Finsupp.sumElim 0 β then c else 0 := by
  classical
  set a : ρ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => e (Sum.inl i)
  set b : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun t => e (Sum.inr t)
  have he : e = Finsupp.sumElim a b := by
    ext (i | i) <;> rfl
  have hmono : monomial e c = c • monomial e (1 : K) := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hmono, map_smul, map_smul, smul_eq_mul, he]
  by_cases ha : a = 0
  · rw [ha, algHom_monomial_tangent ψ hτ, coeff_monomial]
    by_cases hb : β = b
    · subst hb
      simp
    · have hne : Finsupp.sumElim (0 : ρ →₀ ℕ) b ≠ Finsupp.sumElim 0 β := by
        intro h
        apply hb
        ext t
        exact (congrArg (fun x : (ρ ⊕ τ) →₀ ℕ => x (Sum.inr t)) h).symm
      rw [ite_eq_right_iff.mpr (fun h => absurd h hb), mul_zero, ite_eq_right_iff.mpr
        (fun h => absurd h hne)]
  · have hne : Finsupp.sumElim a b ≠ Finsupp.sumElim 0 β := by
      intro h
      apply ha
      ext i
      exact congrArg (fun x : (ρ ⊕ τ) →₀ ℕ => x (Sum.inl i)) h
    rw [algHom_monomial_normal ψ hρ ha, map_zero, mul_zero, ite_eq_right_iff.mpr
      (fun h => absurd h hne)]

/-- Restriction to the tangent directions acts on coefficients by setting the normal exponents to
zero. -/
theorem coeff_algHom_eq_coeff_sumElim [CharZero K] [Fintype ρ] [Fintype τ]
    (hρ : ∀ i, ψ (X (Sum.inl i)) = 0) (hτ : ∀ t, ψ (X (Sum.inr t)) = X t)
    (F : MvPowerSeries (ρ ⊕ τ) K) (β : τ →₀ ℕ) :
    coeff β (ψ F) = coeff (Finsupp.sumElim 0 β) F := by
  classical
  have hψ0 : ∀ i, constantCoeff (ψ (X i)) = 0 := by
    rintro (i | t)
    · rw [hρ, map_zero]
    · rw [hτ, constantCoeff_X]
  set N := β.degree
  set n : (ρ ⊕ τ) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N
  set P : MvPowerSeries (ρ ⊕ τ) K := ∑ e ∈ Finset.Iic n, monomial e (coeff e F)
  have hP : ∀ d, coeff d P = if d ≤ n then coeff d F else 0 := by
    intro d
    simp only [P, map_sum, coeff_monomial]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Iic]
  have hR : ((N + 1 : ℕ) : ℕ∞) ≤ (F - P).order := by
    apply le_order
    intro d hd
    have hd' : d.degree ≤ N := by
      have h : (d.degree : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := hd
      exact Nat.lt_succ_iff.mp (by exact_mod_cast h)
    have hdn : d ≤ n := fun i => (Finsupp.le_degree i d).trans hd'
    rw [map_sub, hP, ite_eq_left hdn, sub_self]
  have h1 : coeff β (ψ (F - P)) = 0 := by
    apply coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N)
      (le_order_algHom_of_le_order ψ hψ0 (N + 1) (F - P) hR)
  have h2 : coeff β (ψ P) = coeff (Finsupp.sumElim 0 β) F := by
    simp only [P, map_sum, coeff_algHom_monomial ψ hρ hτ]
    rw [Finset.sum_ite_eq']
    have hmem : Finsupp.sumElim 0 β ∈ Finset.Iic n := by
      rw [Finset.mem_Iic]
      rintro (i | t)
      · exact Nat.zero_le _
      · exact Finsupp.le_degree t β
    rw [ite_eq_left hmem]
  rw [map_sub, map_sub, h2] at h1
  exact sub_eq_zero.mp h1

end Restriction

variable {r d : ℕ} {V : ℕ → Type*} [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
  [∀ j, FiniteDimensional K (V j)]

/-- §5.2 without fibre directions: if every normal direction has positive old weight and the
restriction to W is ψ ∘ T for a map ψ killing the normal variables and fixing the tangent ones,
then the central slice G_0(j) has at least as many points as the restriction image has
dimensions. -/
theorem restriction_zeroSlice_card_ge [CharZero K] (m₀ : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (w : Fin r ⊕ Fin (d + 1) → ℝ) (v : Fin r ⊕ Fin (d + 1) → ℕ) (hw : ∀ i, 0 ≤ w i)
    (hpos : ∀ i, 0 < w (Sum.inl i)) (hwt : ∀ i, w (Sum.inr i) = 0)
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (ψ : MvPowerSeries (Fin r ⊕ Fin (d + 1)) K →ₐ[K] MvPowerSeries (Fin (d + 1)) K)
    (hρ : ∀ i, ψ (X (Sum.inl i)) = 0) (hτ : ∀ t, ψ (X (Sum.inr t)) = X t) (j : ℕ) :
    Module.finrank K (LinearMap.range (ψ.toLinearMap ∘ₗ T j)) ≤
      (exponentSlice (taylorExponentPoints (weightedMonomialOrder m₀ w v hw) T) j 0).card := by
  refine weighted_zeroSlice_card_ge m₀ w v hw hwt T (fun j => ψ.toLinearMap ∘ₗ T j)
    (fun j s β => (coeff_algHom_eq_coeff_sumElim ψ hρ hτ (T j s) β).symm) ?_ j
  intro j s a ha hne
  exfalso
  obtain ⟨i, hi⟩ := hne
  have hle : w (Sum.inl i) * (a (Sum.inl i) : ℝ) ≤ realExponentWeight w a :=
    Finset.single_le_sum (f := fun k => w k * (a k : ℝ))
      (fun k _ => mul_nonneg (hw k) (Nat.cast_nonneg _)) (Finset.mem_univ (Sum.inl i))
  have hlt : 0 < w (Sum.inl i) * (a (Sum.inl i) : ℝ) :=
    mul_pos (hpos i) (by exact_mod_cast Nat.pos_of_ne_zero hi)
  rw [ha] at hle
  linarith

end MixedFujita
