/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentAdaptedCoordinates
public import MixedFujita.SNCComponentExceptionalCoefficients
public import MixedFujita.EffectiveCartierIdealProduct

/-! Component-sensitive total transforms for the actual single blow-up.
The incidence is tested against each component of the original centre.
The resulting product of actual ideals retains all scheme multiplicities. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

theorem snc_disconnectedCentre_strictTransform_ideal_product
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    (a : D.ι) :
    (D.component a).comap Z.blowUpπ = (D.component a).strictTransform Z *
      ∏ j, if D.component a ≤ Z.componentFamily.component j then
        (Z.componentFamily.component j).comap Z.blowUpπ else ⊤ := by
  classical
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro y
  rw [Scheme.IdealSheafData.stalkIdeal_mul,
    snc_strictTransform_stalk_totalTransform f D Z hD hZ,
    Scheme.IdealSheafData.stalkIdeal_finset_prod]
  congr 1
  by_cases hx : Z.blowUpπ y ∈ Z.support
  · obtain ⟨i, hi⟩ := regularCentre_exists_component_through Z (HasSncWith.isRegular f hZ) _ hx
    rw [sncCentre_component_incidence_iff f D Z hZ i _ _ hi, Finset.prod_eq_single i]
    · split_ifs with h
      · change (Z.comap Z.blowUpπ).stalkIdeal y = _
        rw [Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap,
          Hironaka.Sequence.stalkIdeal_componentFamily_eq Z (HasSncWith.isRegular f hZ) i hi]
      · rw [Scheme.IdealSheafData.stalkIdeal_top]
    · intro j _ hj
      have hoff : Z.blowUpπ y ∉ (Z.componentFamily.component j).support := fun h =>
        hj (Hironaka.Sequence.eq_of_mem_support_componentFamily Z (HasSncWith.isRegular f hZ) h hi)
      split_ifs
      · rw [Scheme.IdealSheafData.stalkIdeal_comap,
          Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hoff, Ideal.map_top,
          Ideal.one_eq_top]
      · rw [Scheme.IdealSheafData.stalkIdeal_top, Ideal.one_eq_top]
    · exact fun h => (h (Finset.mem_univ i)).elim
  · have he : Z.exceptionalDivisor.stalkIdeal y = ⊤ := by
      change (Z.comap Z.blowUpπ).stalkIdeal y = _
      rw [Scheme.IdealSheafData.stalkIdeal_comap,
        Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hx, Ideal.map_top]
    rw [he, ite_self, ← Ideal.one_eq_top]
    symm
    apply Finset.prod_eq_one
    intro j _
    have hoff : Z.blowUpπ y ∉ (Z.componentFamily.component j).support :=
      fun h => hx (centre_component_support_subset Z j h)
    split_ifs
    · rw [Scheme.IdealSheafData.stalkIdeal_comap,
        Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ hoff, Ideal.map_top,
        Ideal.one_eq_top]
    · rw [Scheme.IdealSheafData.stalkIdeal_top, Ideal.one_eq_top]

theorem snc_disconnectedCentre_cartier_totalTransform
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp] [IsDominant Z.blowUpπ]
    (a : D.ι) (P : CartierDivisor X) (hP : P.IsEffective)
    (hPI : effectiveCartierIdealSheaf P hP = D.component a)
    (G : CartierDivisor Z.blowUp) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (D.component a).strictTransform Z)
    (E : Z.componentFamily.ι → CartierDivisor Z.blowUp) (hE : ∀ i, (E i).IsEffective)
    (hEI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
      (Z.componentFamily.component i).comap Z.blowUpπ) :
    cartierPullback Z.blowUpπ P = G + ∑ i,
      if D.component a ≤ Z.componentFamily.component i then E i else 0 := by
  classical
  let F := fun i => if D.component a ≤ Z.componentFamily.component i then E i else 0
  have hF : ∀ i, (F i).IsEffective := by
    intro i
    dsimp only [F]
    split_ifs
    · exact hE i
    · exact CartierDivisor.isEffective_zero
  apply cartierPullback_eq_add_of_ideal_product Z.blowUpπ P hP G _ hG
    (effectiveCartier_finset_sum Finset.univ F hF)
  rw [hPI, hGI, effectiveCartierIdealSheaf_finset_sum Finset.univ F hF,
    snc_disconnectedCentre_strictTransform_ideal_product f D Z hD hZ a]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [F]
  split_ifs with h
  · exact (hEI i).symm
  · exact (effectiveCartierIdealSheaf_zero_eq_top _).symm

end MixedFujita
