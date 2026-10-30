/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentCentreData
public import MixedFujita.SNCStrictTransformPrimes
public import MixedFujita.InvertibleIdealCartier
public import Hironaka.Scheme.BlowUp.Composite

/-! Reduced coefficient profiles for the actual component exceptional
divisors, without choosing their generic points. The stalk of the selected
component centre equals the stalk of the whole centre; the SNC exceptional
equation is therefore a uniformizer for the component divisor as well. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

theorem snc_componentExceptional_cartierCoefficient
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [NoetherianSpace X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp]
    (i : Z.componentFamily.ι) (E : CartierDivisor Z.blowUp) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = (Z.componentFamily.component i).comap Z.blowUpπ)
    (t : CodimensionOnePoint Z.blowUp) :
    cartierCoefficient E (t : Z.blowUp) =
      if Z.blowUpπ (t : Z.blowUp) ∈ (Z.componentFamily.component i).support then 1 else 0 := by
  let := isRegularLocalRing_stalk_blowUp' f D.component Z (hasSncWith_data D Z hZ) (t : Z.blowUp)
  let : IsDiscreteValuationRing (Z.blowUp.presheaf.stalk (t : Z.blowUp)) := inferInstance
  by_cases ht : Z.blowUpπ (t : Z.blowUp) ∈ (Z.componentFamily.component i).support
  · rw [ite_eq_left ht]
    have hsm : IsSmoothDivisor Z.exceptionalDivisor :=
      isSmoothDivisor_totalTransform_component f D Z hD hZ (toLex (Sum.inr PUnit.unit))
    have htz : (t : Z.blowUp) ∈ Z.exceptionalDivisor.support :=
      (mem_support_comap_iff_apply Z Z.blowUpπ _).mpr (centre_component_support_subset Z i ht)
    obtain ⟨a, ha, ha2, hIa⟩ := hsm.2 _ htz
    have hst : (effectiveCartierIdealSheaf E hE).stalkIdeal (t : Z.blowUp) =
        Z.exceptionalDivisor.stalkIdeal (t : Z.blowUp) := by
      rw [hEI]
      change ((Z.componentFamily.component i).comap Z.blowUpπ).stalkIdeal _ =
        (Z.comap Z.blowUpπ).stalkIdeal _
      rw [Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap,
        Hironaka.Sequence.stalkIdeal_componentFamily_eq Z (HasSncWith.isRegular f hZ) i ht]
    apply effectiveCartier_coefficient_of_stalkIdeal_span E hE t a
      (fun h => ha2 (h ▸ Ideal.zero_mem _)) (hst.trans hIa) 1
    exact (localAdicOrder_eq_nat_iff a 1).mpr ⟨by simpa only [pow_one] using ha, ha2⟩
  · rw [ite_eq_right ht]
    apply cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf E hE _
    rw [hEI, Scheme.IdealSheafData.support_comap]
    exact ht

/-- Construct strict-transform prime profiles and component exceptional
support profiles from the original SNC geometry, without connectedness. -/
theorem snc_disconnectedCentre_exists_cartier_support_profiles
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support)
    (ξ : D.ι → X) (hinj : Function.Injective ξ) (hcod : ∀ i, Order.coheight (ξ i) = 1)
    (hgen : ∀ i, IsGenericPoint (ξ i) ((D.component i).support : Set X))
    (havoid : ∀ i, ξ i ∉ Z.support) :
    let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
    let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
    ∃ (ξ' : D.ι → Z.blowUp) (G : D.ι → CartierDivisor Z.blowUp)
      (E : Z.componentFamily.ι → CartierDivisor Z.blowUp),
      ∃ (hG : ∀ i, (G i).IsEffective) (hE : ∀ j, (E j).IsEffective),
      Function.Injective ξ' ∧
      (∀ i, Z.blowUpπ (ξ' i) = ξ i) ∧
      (∀ i, effectiveCartierIdealSheaf (G i) (hG i) = (D.component i).strictTransform Z) ∧
      (∀ j, effectiveCartierIdealSheaf (E j) (hE j) =
        (Z.componentFamily.component j).comap Z.blowUpπ) ∧
      (∀ i (t : CodimensionOnePoint Z.blowUp), cartierCoefficient (G i) (t : Z.blowUp) =
        if (t : Z.blowUp) = ξ' i then 1 else 0) ∧
      (∀ j (t : CodimensionOnePoint Z.blowUp), cartierCoefficient (E j) (t : Z.blowUp) =
        if Z.blowUpπ (t : Z.blowUp) ∈ (Z.componentFamily.component j).support then 1 else 0) ∧
      (∀ i j, Z.blowUpπ (ξ' i) ∉ (Z.componentFamily.component j).support) := by
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  let : Z.blowUp.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from Z.blowUpπ]
    infer_instance⟩
  obtain ⟨E, hE, hEI, _, _⟩ := regularCentre_exists_component_exceptional_cartier Z
    (HasSncWith.isRegular f hZ) hη
  choose G hG hGI using fun i => exists_effectiveCartier_of_invertibleIdeal _
    (snc_strictTransform_isInvertible f D Z hD hZ i)
  obtain ⟨ξ', hinj', hπ, _, _, hGc, _⟩ :=
    snc_exists_strictTransform_primeProfiles f D Z hD hZ ξ hinj hcod hgen havoid G hG hGI
  refine ⟨ξ', G, E, hG, hE, hinj', hπ, hGI, hEI, hGc, ?_, ?_⟩
  · exact fun j => snc_componentExceptional_cartierCoefficient f D Z hD hZ j (E j) (hE j) (hEI j)
  · intro i j h
    rw [hπ i] at h
    exact havoid i (centre_component_support_subset Z j h)

end MixedFujita
