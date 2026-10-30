/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EtaleDVRCoordinateOrder
public import MixedFujita.DVRJacobianOrderBound

@[expose] public section
namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem dvr_derivation_unit_pow_eq_unit_pow_pred
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [IsDomain R]
    [Algebra K R] [IsDiscreteValuationRing R]
    (δ : Derivation K R R) (t : R) (ht : Irreducible t) (hδ : δ t = 1)
    (u : Rˣ) (m : ℕ) (hm : 0 < m) :
    ∃ v : Rˣ, δ ((u : R) * t ^ m) = (v : R) * t ^ (m - 1) := by
  have hcast : IsUnit (m : R) := by
    have hK : IsUnit (m : K) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hm.ne')
    simpa only [map_natCast] using hK.map (algebraMap K R)
  have hunit : IsUnit ((m : R) * (u : R) + t * δ (u : R)) := by
    have htmem : t ∈ IsLocalRing.maximalIdeal R := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using ht.not_isUnit
    have hnot : (m : R) * (u : R) + t * δ (u : R) ∉ IsLocalRing.maximalIdeal R := by
      intro h
      have hterm : t * δ (u : R) ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mul_mem_right _ _ htmem
      have hmu : (m : R) * (u : R) ∈ IsLocalRing.maximalIdeal R := by
        simpa only [add_sub_cancel_right] using Ideal.sub_mem _ h hterm
      have hnu : ¬ IsUnit ((m : R) * (u : R)) := by
        simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmu
      exact hnu (hcast.mul u.isUnit)
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hnot
  obtain ⟨v, hv⟩ := hunit
  refine ⟨v, ?_⟩
  rw [hv, δ.leibniz, δ.leibniz_pow, hδ]
  simp only [smul_eq_mul, nsmul_eq_mul]
  have hp : t ^ m = t * t ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  rw [hp]
  ring

theorem dvr_derivation_exact_positive_order
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [IsDomain R]
    [Algebra K R] [IsDiscreteValuationRing R]
    (δ : Derivation K R R) (t : R) (ht : Irreducible t) (hδ : δ t = 1)
    (f : R) (hf : f ≠ 0) (hfunit : ¬ IsUnit f) :
    ∃ m : ℕ, 0 < m ∧ Ring.ord R f = m ∧
      Ring.ord R (δ f) = (m - 1 : ℕ) ∧ δ f ≠ 0 := by
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf ht
  have hm : 0 < m := by
    by_contra h
    have hzero : m = 0 := by omega
    rw [hzero, pow_zero, mul_one] at hu
    exact hfunit (hu ▸ u.isUnit)
  obtain ⟨v, hv⟩ := dvr_derivation_unit_pow_eq_unit_pow_pred δ t ht hδ u m hm
  refine ⟨m, hm, ?_, ?_, ?_⟩
  · rw [hu, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer ht]
    simp
  · rw [hu, hv, Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer ht]
    simp
  · rw [hu, hv]
    exact mul_ne_zero v.ne_zero (pow_ne_zero _ ht.ne_zero)

end MixedFujita
