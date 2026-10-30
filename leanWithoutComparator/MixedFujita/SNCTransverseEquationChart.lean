/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCTransverseGermChart
public import MixedFujita.SNCActiveStratumChart

/-!
Keep the exact rational equation in the adapted transverse etale chart.
The cut coordinate equals the original regular equation in the actual
function field, including at nonclosed points. This records multiplicity,
not only equality of zero sets.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- Replace one unprotected coordinate to put an actual cut and the old boundary in SNC position. -/
theorem exists_sncChartWith_equation_of_unprotected_coordinate_derivative
    (c : EtaleChart K X n) {r : ℕ} {ξ : Fin r → X} {σ : Fin r → Option (Fin n)}
    (hc : IsSNCChart c ξ σ) (Z : Set X) (g : Γ(X, c.U))
    {x : X} (hx : x ∈ c.U) (j : Fin n)
    (hj : ∀ i, σ i = some j → x ∉ closure ({ξ i} : Set X))
    (hxj : x ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j g))
    (hZg : ∀ z ∈ c.U, z ∈ Z ↔ z ∉ X.basicOpen g) :
    ∃ (c'' : EtaleChart K X n) (σ'' : Fin r → Option (Fin n)) (j : Fin n),
      x ∈ c''.U ∧ IsSNCChartWith c'' ξ σ'' Z (some j) ∧
        (etaleChartCoordinateRationalUnit c'' j : X.functionField) = X.germToFunctionField c.U g := by
  classical
  let S : Set (Fin n) := {a | ∃ i, σ i = some a ∧ x ∈ closure ({ξ i} : Set X)}
  -- the members through x have coordinates in S, which vanish at x
  have hmemS : ∀ i a, σ i = some a → ∀ z ∈ c.U,
      (z ∈ closure ({ξ i} : Set X) ↔ z ∉ X.basicOpen (c.coords (MvPolynomial.X a))) := by
    intro i a hia z hz
    have h := hc.2 i
    rw [hia] at h
    change closure ({ξ i} : Set X) ∩ c.U =
      X.zeroLocus ({c.coords (MvPolynomial.X a)} : Set Γ(X, c.U)) ∩ c.U at h
    rw [Scheme.zeroLocus_singleton] at h
    constructor
    · intro hzi
      have hm : z ∈ closure ({ξ i} : Set X) ∩ c.U := ⟨hzi, hz⟩
      rw [h] at hm
      exact hm.1
    · intro hzb
      have hm : z ∈ ((X.basicOpen (c.coords (MvPolynomial.X a)) : Set X))ᶜ ∩ c.U := ⟨hzb, hz⟩
      rw [← h] at hm
      exact hm.1
  have hnone : ∀ i, σ i = none → ∀ z ∈ c.U, z ∉ closure ({ξ i} : Set X) := by
    intro i hi z hz hzi
    have h := hc.2 i
    rw [hi] at h
    change closure ({ξ i} : Set X) ∩ c.U = ∅ at h
    have hm : z ∈ closure ({ξ i} : Set X) ∩ c.U := ⟨hzi, hz⟩
    rw [h] at hm
    exact hm
  have hjS : j ∉ S := by
    rintro ⟨i, hi, hxi⟩
    exact hj i hi hxi
  let c' := etaleChartReplace c j g ⟨⟨x, hxj⟩⟩
  -- the members not through x
  let C : Set X := ⋃ i ∈ {i | x ∉ closure ({ξ i} : Set X)}, closure ({ξ i} : Set X)
  have hC : IsClosed C :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun i _ => isClosed_closure
  have hxC : x ∉ C := by
    simp only [C, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
    intro i hi hxi
    exact hi hxi
  obtain ⟨h, hle, hxh⟩ :=
    c'.isAffine.exists_basicOpen_le (V := ⟨Cᶜ, hC.isOpen_compl⟩) ⟨x, hxC⟩ hxj
  let c'' := etaleChartBasicOpen c' h ⟨⟨x, hxh⟩⟩
  have hU'' : ∀ z ∈ c''.U, z ∈ c'.U ∧ z ∈ c.U ∧ z ∉ C := fun z hz =>
    ⟨X.basicOpen_le h hz, X.basicOpen_le _ (X.basicOpen_le h hz), hle hz⟩
  -- coordinates of c'' at its points
  have hcoord_ne : ∀ a, a ≠ j → ∀ z ∈ c''.U,
      (z ∈ X.basicOpen (c''.coords (MvPolynomial.X a)) ↔
        z ∈ X.basicOpen (c.coords (MvPolynomial.X a))) := by
    intro a haj z hz
    change z ∈ X.basicOpen (sectionBasicOpenRestrict (K := K) h
      (c'.coords (MvPolynomial.X a))) ↔ _
    rw [mem_basicOpen_sectionBasicOpenRestrict h _ hz,
      etaleChartReplace_coords_ne c j g _ haj,
      mem_basicOpen_sectionBasicOpenRestrict _ _ (hU'' z hz).1]
  have hcoord_self : ∀ z ∈ c''.U,
      (z ∈ X.basicOpen (c''.coords (MvPolynomial.X j)) ↔ z ∈ X.basicOpen g) := by
    intro z hz
    change z ∈ X.basicOpen (sectionBasicOpenRestrict (K := K) h
      (c'.coords (MvPolynomial.X j))) ↔ _
    rw [mem_basicOpen_sectionBasicOpenRestrict h _ hz, etaleChartReplace_coords_self,
      mem_basicOpen_sectionBasicOpenRestrict _ _ (hU'' z hz).1]
  have hσS : ∀ i a, (if x ∈ closure ({ξ i} : Set X) then σ i else none) = some a →
      σ i = some a ∧ a ∈ S := by
    intro i a hia
    by_cases hxi : x ∈ closure ({ξ i} : Set X)
    · rw [if_pos hxi] at hia
      exact ⟨hia, i, hia, hxi⟩
    · rw [if_neg hxi] at hia
      exact absurd hia (by simp)
  have hEq : (etaleChartCoordinateRationalUnit c'' j : X.functionField) =
      X.germToFunctionField c.U g := by
    simp only [etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
    change X.germToFunctionField c''.U
      (sectionBasicOpenRestrict (K := K) h (c'.coords (MvPolynomial.X j))) = _
    change X.germToFunctionField c''.U
      (X.presheaf.map (homOfLE (X.basicOpen_le h)).op (c'.coords (MvPolynomial.X j))) = _
    calc
      _ = X.germToFunctionField c'.U (c'.coords (MvPolynomial.X j)) := by
        convert germToFunctionField_restrict X (X.basicOpen_le h)
          (c'.coords (MvPolynomial.X j)) using 1 <;> rfl
      _ = X.germToFunctionField c.U g := by
        rw [etaleChartReplace_coords_self]
        change X.germToFunctionField c'.U
          (X.presheaf.map (homOfLE (X.basicOpen_le
            (etaleCoordinateDerivation c.coords c.formallyEtale j g))).op g) = _
        convert germToFunctionField_restrict X _ g using 1 <;> rfl

  refine ⟨c'', fun i => if x ∈ closure ({ξ i} : Set X) then σ i else none, j, hxh,
    ⟨⟨fun i i' a hi hi' => hc.1 i i' a (hσS i a hi).1 (hσS i' a hi').1, fun i => ?_⟩,
      fun i b hib => ?_, ?_⟩, hEq⟩
  · -- the members of the family
    by_cases hxi : x ∈ closure ({ξ i} : Set X)
    · have hσi : ∃ a, σ i = some a := by
        cases hσ : σ i with
        | none => exact absurd hxi (hnone i hσ x hx)
        | some a => exact ⟨a, rfl⟩
      obtain ⟨a, hia⟩ := hσi
      have haj : a ≠ j := fun haj => hjS (haj ▸ ⟨i, hia, hxi⟩)
      simp only [if_pos hxi, hia]
      change closure ({ξ i} : Set X) ∩ c''.U =
        X.zeroLocus ({c''.coords (MvPolynomial.X a)} : Set Γ(X, c''.U)) ∩ c''.U
      rw [Scheme.zeroLocus_singleton]
      ext z
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
      constructor
      · rintro ⟨hzi, hz⟩
        exact ⟨(hcoord_ne a haj z hz).not.mpr ((hmemS i a hia z (hU'' z hz).2.1).mp hzi), hz⟩
      · rintro ⟨hzb, hz⟩
        exact ⟨(hmemS i a hia z (hU'' z hz).2.1).mpr ((hcoord_ne a haj z hz).not.mp hzb), hz⟩
    · simp only [if_neg hxi]
      change closure ({ξ i} : Set X) ∩ c''.U = ∅
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hzi hz
      exact (hU'' z hz).2.2 (Set.mem_biUnion (x := i) hxi hzi)
  · -- the coordinate of the zero locus is not one of the family
    intro hjb
    have hjb' : j = b := Option.some_injective _ hjb
    exact hjS (hjb' ▸ (hσS i b hib).2)
  · -- the zero locus
    change Z ∩ c''.U =
      X.zeroLocus ({c''.coords (MvPolynomial.X j)} : Set Γ(X, c''.U)) ∩ c''.U
    rw [Scheme.zeroLocus_singleton]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨hzZ, hz⟩
      exact ⟨(hcoord_self z hz).not.mpr ((hZg z (hU'' z hz).2.1).mp hzZ), hz⟩
    · rintro ⟨hzb, hz⟩
      exact ⟨(hZg z (hU'' z hz).2.1).mpr ((hcoord_self z hz).not.mp hzb), hz⟩

/-- Actual stalk transversality produces an adapted etale SNC chart at any scheme point. -/
theorem exists_sncChartWith_equation_of_transverse_germ [PerfectField K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) {r : ℕ} {ξ : Fin r → X} {σ : Fin r → Option (Fin n)}
    (hc : IsSNCChart c ξ σ) (Z : Set X) (g : Γ(X, c.U))
    {x : X} (hx : x ∈ c.U)
    (hg : X.presheaf.germ c.U x hx g ∈ maximalIdeal (X.presheaf.stalk x))
    (htrans : X.presheaf.germ c.U x hx g ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔
      Ideal.span (Set.range fun a : {a : Fin n // ∃ i, σ i = some a ∧ x ∈ closure ({ξ i} : Set X)} =>
        X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a.1))))
    (hZg : ∀ z ∈ c.U, z ∈ Z ↔ z ∉ X.basicOpen g) :
    ∃ (c'' : EtaleChart K X n) (σ'' : Fin r → Option (Fin n)) (j : Fin n),
      x ∈ c''.U ∧ IsSNCChartWith c'' ξ σ'' Z (some j) ∧
        (etaleChartCoordinateRationalUnit c'' j : X.functionField) = X.germToFunctionField c.U g := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun a => ∃ i, σ i = some a ∧ x ∈ closure ({ξ i} : Set X)
  have hS : ∀ j ∈ S, X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X j)) ∈
      maximalIdeal (X.presheaf.stalk x) := by
    intro j hj
    obtain ⟨i, hi, hxi⟩ := (Finset.mem_filter.mp hj).2
    have hset := hc.2 i
    rw [hi, Option.elim_some] at hset
    have hm : x ∈ X.zeroLocus ({c.coords (MvPolynomial.X j)} : Set Γ(X, c.U)) ∩ c.U :=
      hset ▸ ⟨hxi, hx⟩
    rw [Scheme.zeroLocus_singleton] at hm
    exact (mem_maximalIdeal _).mpr (fun hu => hm.1 ((X.mem_basicOpen _ x hx).mpr hu))
  have hrange : (Set.range fun a : S => X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a.1))) =
      Set.range (fun a : {a : Fin n // ∃ i, σ i = some a ∧ x ∈ closure ({ξ i} : Set X)} =>
        X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a.1))) := by
    ext t
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.1, (Finset.mem_filter.mp a.2).2⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩⟩, rfl⟩
  have htransS : X.presheaf.germ c.U x hx g ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔
      Ideal.span (Set.range fun a : S => X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a.1))) := by
    rwa [hrange]
  obtain ⟨j, hjS, hxj⟩ := exists_coordinateDerivation_mem_basicOpen_of_transverse_germ
    c S g x hx hS hg htransS
  apply exists_sncChartWith_equation_of_unprotected_coordinate_derivative c hc Z g hx j _ hxj hZg
  intro i hi hxi
  exact hjS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hi, hxi⟩)

/-- The intrinsic active-stratum condition gives the exact equation in the adapted chart. -/
theorem exists_sncChartWith_equation_of_active_stratum_transverse_germ [PerfectField K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X) (σ : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σ) (Z : Set X) (g : Γ(X, c.U)) (x : X) (hx : x ∈ c.U)
    (hg : X.presheaf.germ c.U x hx g ∈ maximalIdeal (X.presheaf.stalk x))
    (htrans : X.presheaf.germ c.U x hx g ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔
      (sncActiveStratumIdeal (sncDivisorFamilyOfPoints ξ) x).stalkIdeal x)
    (hZg : ∀ z ∈ c.U, z ∈ Z ↔ z ∉ X.basicOpen g) :
    ∃ (c' : EtaleChart K X n) (σ' : Fin r → Option (Fin n)) (j : Fin n),
      x ∈ c'.U ∧ IsSNCChartWith c' ξ σ' Z (some j) ∧
        (etaleChartCoordinateRationalUnit c' j : X.functionField) = X.germToFunctionField c.U g := by
  rw [sncActiveStratumIdeal_stalk_eq_chart_span c ξ σ hc x hx] at htrans
  exact exists_sncChartWith_equation_of_transverse_germ c hc Z g hx hg htrans hZg

end MixedFujita
