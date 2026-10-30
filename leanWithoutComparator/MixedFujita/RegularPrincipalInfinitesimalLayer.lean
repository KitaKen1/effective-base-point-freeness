/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import TauCeti.RingTheory.DedekindDomain.Ideal.QuotientPow
public import Mathlib.LinearAlgebra.Isomorphisms

/-! Actual adjacent quotient kernels for a regular principal ideal.
Multiplication by `t^m` identifies `R/(t)` with the kernel of
`R/(t)^(m+1) → R/(t)^m`. No domain, maximality or dimension assumption
is needed: regularity of the chosen equation suffices. -/

@[expose] public section
namespace MixedFujita
variable {R : Type*} [CommRing R]

noncomputable def principalInfinitesimalTransition (t : R) (m : ℕ) :
    (R ⧸ (Ideal.span {t}) ^ (m + 1)) →ₗ[R] (R ⧸ (Ideal.span {t}) ^ m) :=
  Submodule.factor (Ideal.pow_le_pow_right (I := Ideal.span {t}) m.le_succ)

noncomputable def principalInfinitesimalLayerMap (t : R) (m : ℕ) :
    (R ⧸ Ideal.span {t}) →ₗ[R] (R ⧸ (Ideal.span {t}) ^ (m + 1)) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R (t ^ m))
    (Ideal.le_comap_mulLeft_pow_succ
      (show t ^ m ∈ (Ideal.span {t}) ^ m by
        rw [Ideal.span_singleton_pow]
        exact Ideal.subset_span (Set.mem_singleton _)))

theorem principalInfinitesimalLayerMap_mk (t x : R) (m : ℕ) :
    principalInfinitesimalLayerMap t m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (t ^ m * x) := rfl

theorem principalInfinitesimalLayerMap_injective (t : R)
    (ht : t ∈ nonZeroDivisors R) (m : ℕ) :
    Function.Injective (principalInfinitesimalLayerMap t m) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro y hy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [principalInfinitesimalLayerMap_mk, Submodule.Quotient.mk_eq_zero,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
  obtain ⟨z, hz⟩ := hy
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [Ideal.mem_span_singleton]
  refine ⟨z, ?_⟩
  have hc := (isRegular_iff_mem_nonZeroDivisors.mpr ht).left.pow m
  apply hc
  simpa only [pow_succ, mul_assoc] using hz

theorem principalInfinitesimalLayerMap_exact (t : R) (m : ℕ) :
    Function.Exact (principalInfinitesimalLayerMap t m)
      (principalInfinitesimalTransition t m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change Submodule.Quotient.mk (p := (Ideal.span {t}) ^ m) x = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [principalInfinitesimalLayerMap_mk, Submodule.Quotient.eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
    obtain ⟨b, hb⟩ := hz
    refine ⟨a - t * b, ?_⟩
    rw [pow_succ] at hb
    linear_combination -hb

/-- A canonical coordinate map into the actual kernel, obtained from exactness. -/
noncomputable def principalInfinitesimalLayerEquiv (t : R)
    (ht : t ∈ nonZeroDivisors R) (m : ℕ) :
    (R ⧸ Ideal.span {t}) ≃ₗ[R] LinearMap.ker (principalInfinitesimalTransition t m) :=
  LinearEquiv.ofBijective
    ((principalInfinitesimalLayerMap t m).codRestrict
      (LinearMap.ker (principalInfinitesimalTransition t m))
      (fun x => (principalInfinitesimalLayerMap_exact t m _).mpr ⟨x, rfl⟩)) (by
        constructor
        · intro x y h
          exact principalInfinitesimalLayerMap_injective t ht m (congrArg Subtype.val h)
        · intro y
          obtain ⟨x, hx⟩ := (principalInfinitesimalLayerMap_exact t m y.1).mp y.2
          exact ⟨x, Subtype.ext hx⟩)

theorem principalInfinitesimalLayerEquiv_mk (t : R)
    (ht : t ∈ nonZeroDivisors R) (m : ℕ) (x : R) :
    (principalInfinitesimalLayerEquiv t ht m (Submodule.Quotient.mk x)).val =
      Submodule.Quotient.mk (t ^ m * x) := rfl

/-- Transport the construction along a proved equality of the actual ideal
with the principal ideal of a regular equation. -/
noncomputable def regularPrincipalIdealLayerEquiv (J : Ideal R) (t : R)
    (hJ : J = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (m : ℕ) :
    (R ⧸ J) ≃ₗ[R] LinearMap.ker
      (Submodule.factor (Ideal.pow_le_pow_right (I := J) m.le_succ)) := by
  subst J
  exact principalInfinitesimalLayerEquiv t ht m

theorem regularPrincipalIdealLayerEquiv_mk (J : Ideal R) (t : R)
    (hJ : J = Ideal.span {t}) (ht : t ∈ nonZeroDivisors R) (m : ℕ) (x : R) :
    (regularPrincipalIdealLayerEquiv J t hJ ht m (Submodule.Quotient.mk x)).val =
      Submodule.Quotient.mk (t ^ m * x) := by
  subst J
  rfl

end MixedFujita
