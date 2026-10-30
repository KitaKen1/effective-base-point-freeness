/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
public import Hironaka.Scheme.Snc.TotalTransformChartComputation
public import Hironaka.Scheme.Snc.TotalTransformOffCentre
public import Hironaka.Scheme.Snc.HasSncWith
public import Hironaka.Scheme.BlowUp.Descent
public import Hironaka.Scheme.BlowUpSequence.PullbackSnc
public import Hironaka.Scheme.IdealSheaf.StalkLe
public import Hironaka.Scheme.IdealSheaf.StalkIdeal
public import Hironaka.Scheme.IdealSheaf.Order.Basic
public import Hironaka.Scheme.IdealSheaf.Invertible

/-! Actual SNC strict transforms and total transforms, including multiplicities.
The local containment test chooses whether the exceptional ideal occurs.
A uniform containment test then yields a global ideal-sheaf identity. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open Scheme Scheme.IdealSheafData
namespace MixedFujita
universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem smoothDivisor_isInvertible {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] (D : Y.IdealSheafData)
    (hD : IsSmoothDivisor D) : D.IsInvertible := by
  apply isInvertible_of_forall_stalkIdeal_eq_span
  intro y
  by_cases hy : y ∈ D.support
  · obtain ⟨a, _, ha, hI⟩ := hD.2 y hy
    refine ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ?_, hI⟩
    intro hzero
    exact ha (hzero ▸ Ideal.zero_mem _)
  · exact ⟨1, one_mem _, (stalkIdeal_eq_top_of_notMem_support D hy).trans
      Ideal.span_singleton_one.symm⟩

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)

include f hD hZ

theorem snc_strictTransform_stalk_totalTransform (i : D.ι) (y : Z.blowUp) :
    ((D.component i).comap Z.blowUpπ).stalkIdeal y =
      ((D.component i).strictTransform Z).stalkIdeal y *
        (if (D.component i).stalkIdeal (Z.blowUpπ y) ≤ Z.stalkIdeal (Z.blowUpπ y)
          then Z.exceptionalDivisor.stalkIdeal y else ⊤) := by
  by_cases hy : y ∈ Z.exceptionalDivisor.support
  · have hx : Z.blowUpπ y ∈ Z.support :=
      (mem_support_comap_iff_apply Z Z.blowUpπ y).mp hy
    by_cases hxi : Z.blowUpπ y ∈ (D.component i).support
    · obtain ⟨n, z, hz, s, hs⟩ := hZ _ hx
      obtain ⟨c, _, hc⟩ := hz.2
      have hci := hc ⟨i, hxi⟩
      have hiff := IsSncAt.stalkIdeal_le_iff_mem f hz hs hci
      by_cases hcs : c ⟨i, hxi⟩ ∈ s
      · rw [ite_eq_left (hiff.mpr hcs)]
        obtain ⟨e, _, he⟩ := Scheme.IdealSheafData.IsInvertible.exists_mem_nonZeroDivisors_stalkIdeal_eq_span
          (blowUp.isInvertible_comap_π Z) y
        change Z.exceptionalDivisor.stalkIdeal y = Ideal.span {e} at he
        obtain ⟨v, hv, hV⟩ := exists_stalkIdeal_strictTransform_eq_span_of_mem
          f D Z hD hZ i y hy hz hs hci hcs he
        rw [stalkIdeal_comap, hci, Ideal.map_span, Set.image_singleton,
          hv, hV, he, Ideal.span_singleton_mul_span_singleton]
      · rw [ite_eq_right (fun h => hcs (hiff.mp h)), Ideal.mul_top,
          stalkIdeal_strictTransform_of_notMem f D Z hD hZ i y hy hz hs hci hcs,
          stalkIdeal_comap, hci, Ideal.map_span, Set.image_singleton]
    · have htot : ((D.component i).comap Z.blowUpπ).stalkIdeal y = ⊤ := by
        rw [stalkIdeal_comap, stalkIdeal_eq_top_of_notMem_support _ hxi, Ideal.map_top]
      have hstrict : ((D.component i).strictTransform Z).stalkIdeal y = ⊤ := by
        apply top_unique
        rw [← htot]
        exact stalkIdeal_mono (le_saturate _ _) y
      have hnot : ¬ (D.component i).stalkIdeal (Z.blowUpπ y) ≤
          Z.stalkIdeal (Z.blowUpπ y) := by
        rw [stalkIdeal_eq_top_of_notMem_support _ hxi]
        intro h
        have hzmax := (mem_support_iff_stalkIdeal_le_maximalIdeal Z _).mp hx
        exact (IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk (Z.blowUpπ y))).ne_top
          (top_unique (h.trans hzmax))
      rw [htot, hstrict, ite_eq_right hnot, Ideal.mul_top]
  · have he := stalkIdeal_eq_top_of_notMem_support Z.exceptionalDivisor hy
    have hstrict := stalkIdeal_strictTransformAlong_of_notMem_support Z (D.component i) hy
    change ((D.component i).strictTransform Z).stalkIdeal y = _ at hstrict
    rw [stalkIdeal_comap, hstrict, he]
    split_ifs <;> rw [Ideal.mul_top]

/-- Uniform incidence is a condition on the original center and component.
No equality involving the strict transform is an input. -/
theorem snc_strictTransform_totalTransform (i : D.ι) (contains : Prop)
    (hcontains : ∀ x ∈ Z.support,
      (D.component i).stalkIdeal x ≤ Z.stalkIdeal x ↔ contains) :
    (D.component i).comap Z.blowUpπ =
      (D.component i).strictTransform Z * (if contains then Z.exceptionalDivisor else ⊤) := by
  apply ext_stalkIdeal
  intro y
  rw [stalkIdeal_mul, snc_strictTransform_stalk_totalTransform f D Z hD hZ]
  by_cases hy : y ∈ Z.exceptionalDivisor.support
  · have hx := (mem_support_comap_iff_apply Z Z.blowUpπ y).mp hy
    rw [hcontains _ hx]
    split_ifs <;> simp only [stalkIdeal_top]
  · have he := stalkIdeal_eq_top_of_notMem_support Z.exceptionalDivisor hy
    simp only [he, ite_self]
    split_ifs <;> simp only [stalkIdeal_top, he]

theorem snc_strictTransform_isInvertible
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp] (i : D.ι) :
    ((D.component i).strictTransform Z).IsInvertible :=
  smoothDivisor_isInvertible _ (isSmoothDivisor_strictTransform f D Z hD hZ i)

end MixedFujita
