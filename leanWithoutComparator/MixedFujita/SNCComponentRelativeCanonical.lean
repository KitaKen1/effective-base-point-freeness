/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentAdaptedCoordinates
public import MixedFujita.SNCComponentExceptionalCoefficients
public import MixedFujita.SNCBlowupRelativeCanonical
public import MixedFujita.SNCBlowupPrimeCanonicalData

/-! The actual relative canonical divisor for a disconnected SNC centre is
the sum of (component codimension - 1) times the actual component exceptional
divisor. Matched adapted coordinates are constructed on the original base.
No common centre codimension or exceptional generic points are required. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem snc_disconnectedCentre_relativeCanonical_eq_sum
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.Over (Spec (.of k))]
    (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support)
    (c : Z.componentFamily.ι → ℕ) (hcn : ∀ i, c i ≤ n)
    (hdim : ∀ i, SmoothOfRelativeDimension (n - c i)
      ((Z.componentFamily.component i).subschemeι ≫ (X ↘ Spec (.of k))))
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp] [IsDominant Z.blowUpπ]
    (E : Z.componentFamily.ι → CartierDivisor Z.blowUp) (hE : ∀ i, (E i).IsEffective)
    (hEI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
      (Z.componentFamily.component i).comap Z.blowUpπ) :
    let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
    let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
    ∀ (c₀ : EtaleChart k X n) (hX : iSup (fun c : EtaleChart k X n => c.U) = ⊤)
      (cT₀ : EtaleChart k Z.blowUp n) (hT : iSup (fun c : EtaleChart k Z.blowUp n => c.U) = ⊤)
      (hR : IsUnit (chartRelativeJacobianDet Z.blowUpπ c₀ cT₀)),
      relativeCanonicalDivisor n Z.blowUpπ c₀ hX cT₀ hT hR = ∑ i, (c i - 1) • E i := by
  classical
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
  let : Smooth (Z.blowUp ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  dsimp only
  intro c₀ hX cT₀ hT hR
  apply cartierDivisor_eq_of_forall_coefficient_eq
    (smoothScheme_stalk_isIntegrallyClosed (K := k) (n := n))
  intro t
  let := isRegularLocalRing_stalk_blowUp' (X ↘ Spec (.of k)) D.component Z
    (hasSncWith_data D Z hZ) (t : Z.blowUp)
  let : IsDiscreteValuationRing (Z.blowUp.presheaf.stalk (t : Z.blowUp)) := inferInstance
  have hEc := fun i => snc_componentExceptional_cartierCoefficient
    (X ↘ Spec (.of k)) D Z hD hZ i (E i) (hE i) (hEI i) t
  rw [cartierCoefficient_sum]
  simp_rw [cartierCoefficient_nsmul, hEc]
  by_cases htZ : Z.blowUpπ (t : Z.blowUp) ∈ Z.support
  · obtain ⟨i, hi⟩ := regularCentre_exists_component_through Z
      (HasSncWith.isRegular (X ↘ Spec (.of k)) hZ) _ htZ
    have hother : ∀ j, j ≠ i → Z.blowUpπ (t : Z.blowUp) ∉ (Z.componentFamily.component j).support := by
      intro j hj h
      exact hj (Hironaka.Sequence.eq_of_mem_support_componentFamily Z
        (HasSncWith.isRegular (X ↘ Spec (.of k)) hZ) h hi)
    rw [Finset.sum_eq_single i]
    · rw [ite_eq_left hi, mul_one]
      let := hdim i
      obtain ⟨A⟩ := sncCentre_component_exists_adapted_coordinates
        (X ↘ Spec (.of k)) n (c i) D Z hZ i (hcn i) _ hi
      exact coordinateBlowup_matched_relativeCanonical_coefficient A (hcn i)
        c₀ hX cT₀ hT hR t A.mem htZ
    · intro j _ hj
      rw [ite_eq_right (hother j hj), mul_zero]
    · exact fun h => (h (Finset.mem_univ i)).elim
  · have hother : ∀ i, Z.blowUpπ (t : Z.blowUp) ∉ (Z.componentFamily.component i).support :=
      fun i h => htZ (centre_component_support_subset Z i h)
    simp only [ite_eq_right (hother _), mul_zero, Finset.sum_const_zero]
    let := blowUp_isIso_stalkMap_of_notMem_support Z (t : Z.blowUp) htZ
    exact relativeCanonical_coefficient_zero_of_stalkMap_bijective Z.blowUpπ
      c₀ hX cT₀ hT hR t (ConcreteCategory.bijective_of_isIso (Z.blowUpπ.stalkMap (t : Z.blowUp)))

/-- Derive the component codimensions, exceptional Cartier divisors, target
smoothness and function-field comparison, then identify the birational
relative canonical divisor. All geometric data come from the original SNC centre. -/
theorem snc_disconnectedCentre_exists_intrinsic_component_canonical_data
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated] [X.Over (Spec (.of k))]
    (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support) :
    let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
    let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
    let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
    let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
    let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
    let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
      snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
    let hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := k) Z.blowUpπ) :=
      blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη
    ∃ (c : Z.componentFamily.ι → ℕ) (E : Z.componentFamily.ι → CartierDivisor Z.blowUp)
      (hE : ∀ i, (E i).IsEffective),
      (∀ i, 0 < c i ∧ c i ≤ n ∧
        SmoothOfRelativeDimension (n - c i) ((Z.componentFamily.component i).subschemeι ≫ (X ↘ Spec (.of k)))) ∧
      (∀ i, effectiveCartierIdealSheaf (E i) (hE i) =
        (Z.componentFamily.component i).comap Z.blowUpπ) ∧
      (∀ i (t : CodimensionOnePoint Z.blowUp), cartierCoefficient (E i) (t : Z.blowUp) =
        if Z.blowUpπ (t : Z.blowUp) ∈ (Z.componentFamily.component i).support then 1 else 0) ∧
      ∀ (c₀ : EtaleChart k X n) (cT₀ : EtaleChart k Z.blowUp n),
        birationalRelativeCanonicalDivisor n Z.blowUpπ hπ c₀ etaleCharts_cover cT₀ etaleCharts_cover =
          ∑ i, (c i - 1) • E i := by
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
  dsimp only
  obtain ⟨c, hc⟩ := sncCentre_exists_component_codimensions (X ↘ Spec (.of k)) n D Z hZ hη
  obtain ⟨E, hE, hEI, _, _⟩ := regularCentre_exists_component_exceptional_cartier Z
    (HasSncWith.isRegular (X ↘ Spec (.of k)) hZ) hη
  refine ⟨c, E, hE, fun i => ⟨(hc i).1, (hc i).2.1, (hc i).2.2.1⟩, hEI, ?_, ?_⟩
  · exact fun i => snc_componentExceptional_cartierCoefficient
      (X ↘ Spec (.of k)) D Z hD hZ i (E i) (hE i) (hEI i)
  · intro c₀ cT₀
    exact snc_disconnectedCentre_relativeCanonical_eq_sum n D Z hD hZ hη c
      (fun i => (hc i).2.1) (fun i => (hc i).2.2.1) E hE hEI
      c₀ etaleCharts_cover cT₀ etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective Z.blowUpπ
        (blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη) c₀ cT₀)

end MixedFujita
