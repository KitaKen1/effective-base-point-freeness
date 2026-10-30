/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TransverseParameterExtension
public import Hironaka.Algebra.RegularSmooth.Cotangent
public import Hironaka.Scheme.BlowUpSequence.SmoothParameters

/-!
Turn actual cotangent transversality into a differential outside the protected
boundary directions. The residue extension is formally smooth, as holds for
finite type points over a perfect field, so the conormal map is injective.
The resulting coefficient criterion applies at nonclosed points as well.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing KaehlerDifferential
open scoped TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A transverse cotangent class remains outside the protected differential span in the residue fibre. -/
theorem transverse_element_differential_notMem_span
    {K R : Type u} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [Algebra.FormallySmooth K (ResidueField R)] {ι : Type*} [Fintype ι]
    (w : ι → R) (hw : ∀ i, w i ∈ maximalIdeal R) (a : R) (ha : a ∈ maximalIdeal R)
    (htrans : a ∉ maximalIdeal R ^ 2 ⊔ Ideal.span (Set.range w)) :
    (1 : ResidueField R) ⊗ₜ[R] D K R a ∉ Submodule.span (ResidueField R)
      (Set.range fun i => (1 : ResidueField R) ⊗ₜ[R] D K R (w i)) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ResidueField R)).mp h
  have hcot : ∑ i, c i • (maximalIdeal R).toCotangent ⟨w i, hw i⟩ =
      (maximalIdeal R).toCotangent ⟨a, ha⟩ := by
    apply injective_cotangentSpaceToTensor (k := K) (R := R)
    simpa only [map_sum, map_smul, cotangentSpaceToTensor_toCotangent] using hc
  apply htrans
  apply cotangent_mem_span_implies_mem_sq_sup_span w hw a ha
  rw [← hcot]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- Some unprotected coefficient of the differential of a transverse element is a local unit. -/
theorem transverse_element_exists_differential_coefficient_notMem
    {K R : Type u} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    [Algebra.FormallySmooth K (ResidueField R)] {n : ℕ}
    (y : Fin n → R) (S : Finset (Fin n)) (hy : ∀ j ∈ S, y j ∈ maximalIdeal R)
    (a : R) (ha : a ∈ maximalIdeal R)
    (htrans : a ∉ maximalIdeal R ^ 2 ⊔ Ideal.span (Set.range fun j : S => y j))
    (c : Fin n → R) (hD : D K R a = ∑ j, c j • D K R (y j)) :
    ∃ j ∉ S, c j ∉ maximalIdeal R := by
  classical
  by_contra h
  push Not at h
  apply transverse_element_differential_notMem_span (K := K)
    (fun j : S => y j) (fun j => hy j j.2) a ha htrans
  rw [hD, TensorProduct.tmul_sum]
  apply Submodule.sum_mem
  intro j _
  by_cases hj : j ∈ S
  · rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.tmul_eq_smul_one_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  · have hcj := smul_residueField_eq_zero_of_mem (h j hj) (1 : ResidueField R)
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', hcj, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _

end MixedFujita
