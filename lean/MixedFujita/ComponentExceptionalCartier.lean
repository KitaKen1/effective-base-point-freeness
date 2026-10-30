/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InvertibleIdealCartier
public import MixedFujita.EffectiveCartierIdealProduct
public import MixedFujita.HironakaPrincipalizingRound
public import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseBlowUp
public import Hironaka.Scheme.BlowUp.ProductCenter
public import Hironaka.Resolution.Algebraic.Tuning.Transform

/-! Component exceptional divisors on the actual single blow-up.
Invertibility of the product gives invertibility of every factor. Thus the
Cartier family is constructed from the centre ideals, without replacing the
single blow-up by an ordered sequence. The centre need not be connected. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem idealSheaf_isInvertible_of_finset_prod
    {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (h : (∏ i ∈ s, I i).IsInvertible) {i : ι} (hi : i ∈ s) :
    (I i).IsInvertible := by
  classical
  rw [← Finset.mul_prod_erase s I hi] at h
  exact h.of_mul.1

theorem effectiveCartier_finset_sum
    {X : Scheme.{u}} [IsIntegral X] {ι : Type*} (s : Finset ι)
    (D : ι → CartierDivisor X) (hD : ∀ i, (D i).IsEffective) :
    (∑ i ∈ s, D i).IsEffective := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simpa [Finset.sum_insert hi] using (hD i).add ih

theorem effectiveCartierIdealSheaf_finset_sum
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {ι : Type*} (s : Finset ι) (D : ι → CartierDivisor X)
    (hD : ∀ i, (D i).IsEffective) :
    effectiveCartierIdealSheaf (∑ i ∈ s, D i) (effectiveCartier_finset_sum s D hD) =
      ∏ i ∈ s, effectiveCartierIdealSheaf (D i) (hD i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using effectiveCartierIdealSheaf_zero_eq_top
      (CartierDivisor.isEffective_zero (X := X))
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi, Finset.prod_insert hi, ih] using
      effectiveCartierIdealSheaf_add (D i) (∑ j ∈ s, D j) (hD i)
        (effectiveCartier_finset_sum s D hD)

/-- Every regular component of the centre supplies its actual effective
exceptional divisor; their sum is any Cartier representative of the total
exceptional ideal. The supports are pairwise disjoint. -/
theorem regularCentre_exists_component_exceptional_cartier
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [NoetherianSpace X] [X.IsSeparated]
    (Z : X.IdealSheafData) (hZ : IsRegular Z.subscheme)
    (hη : genericPoint X ∉ Z.support) :
    letI := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
    ∃ (E : Z.componentFamily.ι → CartierDivisor Z.blowUp)
      (hE : ∀ i, (E i).IsEffective),
      (∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
        (Z.componentFamily.component i).comap Z.blowUpπ) ∧
      (Pairwise fun i j => Disjoint
        (effectiveCartierIdealSheaf (E i) (hE i)).support
        (effectiveCartierIdealSheaf (E j) (hE j)).support) ∧
      ∀ (F : CartierDivisor Z.blowUp) (hF : F.IsEffective),
        effectiveCartierIdealSheaf F hF = Z.comap Z.blowUpπ →
        F = ∑ i, E i := by
  classical
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  let := LocallyOfFiniteType.isLocallyNoetherian Z.blowUpπ
  let : Z.blowUp.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from Z.blowUpπ]
    infer_instance⟩
  have hprod : (∏ i, (Z.componentFamily.component i).comap Z.blowUpπ) =
      Z.comap Z.blowUpπ := by
    rw [← Scheme.IdealSheafData.comap_finset_prod,
      Hironaka.Sequence.prod_componentFamily_eq Z hZ]
  have hinv : ∀ i, ((Z.componentFamily.component i).comap Z.blowUpπ).IsInvertible := by
    intro i
    apply idealSheaf_isInvertible_of_finset_prod Finset.univ _ _ (Finset.mem_univ i)
    rw [hprod]
    exact Scheme.IdealSheafData.blowUp.isInvertible_comap_π Z
  choose E hE hI using fun i => exists_effectiveCartier_of_invertibleIdeal _ (hinv i)
  refine ⟨E, hE, hI, ?_, ?_⟩
  · intro i j hij
    rw [hI i, hI j, Scheme.IdealSheafData.support_comap,
      Scheme.IdealSheafData.support_comap]
    rw [disjoint_iff, ← SetLike.coe_set_eq, Closeds.coe_inf, Closeds.coe_bot,
      Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hi, hj⟩
    exact hij (Hironaka.Sequence.eq_of_mem_support_componentFamily Z hZ hi hj)
  · intro F hF hFZ
    apply effectiveCartier_eq_of_idealSheaf_eq F _ hF
      (effectiveCartier_finset_sum Finset.univ E hE)
    rw [effectiveCartierIdealSheaf_finset_sum Finset.univ E hE, hFZ]
    simpa only [hI] using hprod.symm

end MixedFujita
