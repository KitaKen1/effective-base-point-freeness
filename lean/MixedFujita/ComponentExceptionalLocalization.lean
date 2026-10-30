/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ComponentExceptionalCartier
public import MixedFujita.RoundupLocalTransport

/-! Exact localization of the component exceptional correction.
Finite disjoint centre supports give ambient isolating opens. On a commuting
dominant square over such an open, the other exceptional Cartier divisors
are exactly zero and the selected divisor is the local exceptional divisor. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem disjoint_idealFamily_exists_isolating_open
    {X : Scheme.{u}} {J : Type*} [Fintype J] (I : J → X.IdealSheafData)
    (hdis : Pairwise fun i j => Disjoint (I i).support (I j).support) (i : J) :
    ∃ U : X.Opens, (I i).support ≤ (U : Set X) ∧
      (∀ j, j ≠ i → (I j).comap U.ι = ⊤) ∧
      (∏ j, I j).comap U.ι = (I i).comap U.ι := by
  classical
  let U : X.Opens := ⨅ j : {j : J // j ≠ i}, (I j.1).support.compl
  have hmem : ∀ x : X, x ∈ U ↔ ∀ j, j ≠ i → x ∉ (I j).support := by
    intro x
    change x ∈ (U : Set X) ↔ _
    simp [U, Opens.coe_iInf, Closeds.compl]
  have hzero : ∀ j, j ≠ i → (I j).comap U.ι = ⊤ := by
    intro j hj
    apply Scheme.IdealSheafData.ext_stalkIdeal
    intro x
    rw [Scheme.IdealSheafData.stalkIdeal_top]
    apply Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support
    rw [Scheme.IdealSheafData.support_comap]
    exact (hmem x.1).mp x.2 j hj
  refine ⟨U, ?_, hzero, ?_⟩
  · intro x hx
    apply (hmem x).mpr
    intro j hj hjx
    have h : Disjoint (I j).support (I i).support := hdis hj
    rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot,
      Set.eq_empty_iff_forall_notMem] at h
    exact h x ⟨hjx, hx⟩
  · rw [Scheme.IdealSheafData.comap_finset_prod]
    apply Finset.prod_eq_single i
    · intro j _ hj
      rw [hzero j hj, Scheme.IdealSheafData.one_eq_top]
    · exact fun h => (h (Finset.mem_univ i)).elim

/-- The isolated component and the whole regular centre have identical
restricted ideal sheaves, including their scheme structure. -/
theorem regularCentre_exists_component_isolating_open
    {X : Scheme.{u}} [NoetherianSpace X] (Z : X.IdealSheafData)
    (hZ : IsRegular Z.subscheme) (i : Z.componentFamily.ι) :
    ∃ U : X.Opens, (Z.componentFamily.component i).support ≤ (U : Set X) ∧
      (∀ j, j ≠ i → (Z.componentFamily.component j).comap U.ι = ⊤) ∧
      Z.comap U.ι = (Z.componentFamily.component i).comap U.ι := by
  have h := disjoint_idealFamily_exists_isolating_open Z.componentFamily.component
    (Hironaka.Sequence.pairwise_disjoint_support_componentFamily Z hZ) i
  simpa only [Hironaka.Sequence.prod_componentFamily_eq Z hZ] using h

theorem cartierPullback_fintype_natural_combination
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    (f : T ⟶ X) [IsDominant f] {J : Type*} [Fintype J]
    (E : J → CartierDivisor X) (k : J → ℕ) :
    cartierPullback f (∑ j, k j • E j) = ∑ j, k j • cartierPullback f (E j) := by
  let pb : CartierDivisor X →+ CartierDivisor T :=
    { toFun := cartierPullback f
      map_zero' := cartierPullback_zero f
      map_add' := cartierPullback_add f }
  exact (map_sum pb _ _).trans (Finset.sum_congr rfl (fun j _ => map_nsmul pb (k j) (E j)))

/-- A component-dependent correction becomes exactly the selected local
exceptional twist. The other terms vanish as Cartier divisors, not just as
line bundle classes. All local maps and ideal equalities are explicit. -/
theorem component_exceptional_decomposition_pullback_square
    {X T S Y : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsIntegral S] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : T ⟶ X) (g : Y ⟶ S) (σ : S ⟶ X) (τ : Y ⟶ T)
    [IsDominant f] [IsDominant g] [IsDominant σ] [IsDominant τ]
    (hsq : τ ≫ f = g ≫ σ) {J : Type*} [Fintype J]
    (I : J → X.IdealSheafData) (i : J)
    (hother : ∀ j, j ≠ i → (I j).comap σ = ⊤)
    (E : J → CartierDivisor T) (hE : ∀ j, (E j).IsEffective)
    (hEI : ∀ j, effectiveCartierIdealSheaf (E j) (hE j) = (I j).comap f)
    (E' : CartierDivisor Y) (hE' : E'.IsEffective)
    (hE'I : effectiveCartierIdealSheaf E' hE' = ((I i).comap σ).comap g)
    (Q : CartierDivisor X) (C : CartierDivisor T) (k : J → ℕ)
    (hC : C = cartierPullback f Q + ∑ j, k j • E j) :
    (∀ j, j ≠ i → cartierPullback τ (E j) = 0) ∧
      cartierPullback τ (E i) = E' ∧
      cartierPullback τ C = cartierPullback g (cartierPullback σ Q) + k i • E' := by
  classical
  have hz : ∀ j, j ≠ i → cartierPullback τ (E j) = 0 := by
    intro j hj
    apply effectiveCartier_eq_of_idealSheaf_eq _ _
      (cartierPullback_isEffective τ (E j) (hE j)) CartierDivisor.isEffective_zero
    rw [effectiveCartierIdealSheaf_cartierPullback τ (E j) (hE j), hEI,
      ← Scheme.IdealSheafData.comap_comp, hsq, Scheme.IdealSheafData.comap_comp,
      hother j hj, Scheme.IdealSheafData.comap_top, effectiveCartierIdealSheaf_zero_eq_top]
  have he := effective_cartier_pullback_eq_of_center_square f g σ τ hsq (I i)
    ((I i).comap σ) rfl (E i) (hE i) (hEI i) E' hE' hE'I
  refine ⟨hz, he, ?_⟩
  rw [hC, cartierPullback_add, cartierPullback_fintype_natural_combination,
    ← cartierPullback_comp, cartierPullback_congr_hom hsq, cartierPullback_comp]
  congr 1
  rw [Finset.sum_eq_single i, he]
  · intro j _ hj
    rw [hz j hj, smul_zero]
  · exact fun h => (h (Finset.mem_univ i)).elim

end MixedFujita
