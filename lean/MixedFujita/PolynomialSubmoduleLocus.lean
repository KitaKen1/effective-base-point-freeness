/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasisAttainmentAbstract
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Polynomial families of vectors land in a fixed subspace on an actual polynomial zero set.
Equations are obtained by applying every linear functional that vanishes on the subspace.
The ambient vector space need not be finite dimensional; the family has finitely many vectors.
This retains cancellations among the moving coefficients. Intersections and finite unions of
such loci are also represented by ideals, for use with fixed divisorial tests.
-/

@[expose] public section

open scoped BigOperators

namespace MixedFujita

/-- Equations detecting membership of a polynomial vector family in a fixed subspace. -/
noncomputable def submoduleMembershipIdeal {σ K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {m : ℕ} (W : Submodule K V) (b : Fin m → V)
    (L : Fin m → MvPolynomial σ K) : Ideal (MvPolynomial σ K) :=
  Ideal.span {p | ∃ ℓ : Module.Dual K V, ℓ ∈ W.dualAnnihilator ∧
    p = ∑ k, MvPolynomial.C (ℓ (b k)) * L k}

/-- The equations from the annihilator detect the actual subspace, not merely its span or a
chosen finite-dimensional quotient. -/
theorem mem_polynomialZeroSet_submoduleMembershipIdeal {σ K V : Type*} [Finite σ] [Field K]
    [AddCommGroup V] [Module K V] {m : ℕ} (W : Submodule K V) (b : Fin m → V)
    (L : Fin m → MvPolynomial σ K) (c : σ → K) :
    c ∈ polynomialZeroSet (submoduleMembershipIdeal W b L) ↔
      (∑ k, MvPolynomial.eval c (L k) • b k) ∈ W := by
  classical
  have heval : ∀ ℓ : Module.Dual K V,
      MvPolynomial.eval c (∑ k, MvPolynomial.C (ℓ (b k)) * L k) =
        ℓ (∑ k, MvPolynomial.eval c (L k) • b k) := by
    intro ℓ
    simp only [map_sum, map_mul, MvPolynomial.eval_C, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  constructor
  · intro hc
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp
    intro ℓ hℓ
    rw [← heval]
    exact hc _ (Ideal.subset_span ⟨ℓ, hℓ, rfl⟩)
  · intro hw
    have hle : submoduleMembershipIdeal W b L ≤ RingHom.ker (MvPolynomial.eval c) := by
      apply Ideal.span_le.mpr
      rintro p ⟨ℓ, hℓ, rfl⟩
      change MvPolynomial.eval c _ = 0
      rw [heval]
      exact (Submodule.mem_dualAnnihilator ℓ).mp hℓ _ hw
    exact fun p hp => hle hp

/-- An arbitrary simultaneous family of polynomial equations is represented by the supremum
of its ideals. -/
theorem mem_polynomialZeroSet_iSup {ι σ K : Type*} [Finite σ] [Field K]
    (I : ι → Ideal (MvPolynomial σ K)) (c : σ → K) :
    c ∈ polynomialZeroSet (⨆ i, I i) ↔ ∀ i, c ∈ polynomialZeroSet (I i) := by
  constructor
  · intro h i p hp
    exact h p (le_iSup I i hp)
  · intro h
    have hle : (⨆ i, I i) ≤ RingHom.ker (MvPolynomial.eval c) :=
      iSup_le fun i p hp => h i p hp
    exact fun p hp => hle hp

/-- Intersecting the ideals corresponds to the union of their K-point zero sets. -/
theorem polynomialZeroSet_inf {σ K : Type*} [Finite σ] [Field K]
    (I J : Ideal (MvPolynomial σ K)) :
    polynomialZeroSet (I ⊓ J) = polynomialZeroSet I ∪ polynomialZeroSet J := by
  classical
  ext c
  constructor
  · intro h
    by_contra hnone
    have hI : c ∉ polynomialZeroSet I := fun hc => hnone (Or.inl hc)
    have hJ : c ∉ polynomialZeroSet J := fun hc => hnone (Or.inr hc)
    obtain ⟨p, hpc⟩ := not_forall.mp hI
    obtain ⟨hp, hpc⟩ := not_imp.mp hpc
    obtain ⟨q, hq⟩ := not_forall.mp hJ
    obtain ⟨hq, hqc⟩ := not_imp.mp hq
    have hprod := h (p * q) ⟨I.mul_mem_right q hp, J.mul_mem_left p hq⟩
    rw [map_mul] at hprod
    exact (mul_ne_zero hpc hqc) hprod
  · rintro (h | h) p hp
    · exact h p hp.1
    · exact h p hp.2

/-- The zero set of the unit ideal is empty. -/
theorem polynomialZeroSet_top {σ K : Type*} [Finite σ] [Field K] :
    polynomialZeroSet (⊤ : Ideal (MvPolynomial σ K)) = ∅ := by
  ext c
  constructor
  · intro hc
    have h := hc 1 (by trivial)
    simpa using h
  · exact False.elim

/-- A finite union of given polynomial zero sets is represented by a single ideal. No infinite
union assertion is made. -/
theorem exists_polynomialIdeal_finite_union {ι σ K : Type*} [Finite ι] [Finite σ] [Field K]
    (I : ι → Ideal (MvPolynomial σ K)) :
    ∃ J : Ideal (MvPolynomial σ K), (⋃ i, polynomialZeroSet (I i)) = polynomialZeroSet J := by
  classical
  letI := Fintype.ofFinite ι
  let S : Finset ι := Finset.univ
  have hfinite : ∀ S : Finset ι,
      ∃ J : Ideal (MvPolynomial σ K), (⋃ i ∈ S, polynomialZeroSet (I i)) = polynomialZeroSet J := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨⊤, by simp [polynomialZeroSet_top]⟩
    | @insert i S hi ih =>
      obtain ⟨J, hJ⟩ := ih
      refine ⟨I i ⊓ J, ?_⟩
      rw [polynomialZeroSet_inf, ← hJ]
      simp
  obtain ⟨J, hJ⟩ := hfinite S
  exact ⟨J, by simpa [S] using hJ⟩

end MixedFujita
