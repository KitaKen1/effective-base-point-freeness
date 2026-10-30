/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCExceptionalPrime
public import MixedFujita.SNCBlowupRelativeCanonical

/-! The actual prime data and relative canonical divisor of a connected SNC
blow-up, for specified smooth relative dimensions. Blow-up integrality,
dominance, smoothness, function-field bijectivity, chart coverings, exceptional
Cartier representative and all coefficient profiles are constructed internally.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem blowUp_functionField_bijective_of_genericPoint_notMem_support
    {X : Scheme.{u}} [IsIntegral X] (Z : X.IdealSheafData)
    [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ] (hη : genericPoint X ∉ Z.support) :
    Function.Bijective (dominantFunctionFieldMap Z.blowUpπ).hom := by
  apply dominantFunctionFieldMap_bijective_of_isIso_stalkMap
  apply blowUp_isIso_stalkMap_of_notMem_support
  rw [dominant_map_genericPoint]
  exact hη

set_option maxHeartbeats 1000000 in
theorem snc_connectedCentre_exists_full_cartier_prime_canonical_data
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] [X.Over (Spec (.of k))]
    (n r : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ (X ↘ Spec (.of k)))] (hrn : r ≤ n) (hr : 0 < r)
    [IsNoetherian Z.subscheme] [ConnectedSpace Z.subscheme]
    (hη : genericPoint X ∉ Z.support)
    (ξ : D.ι → X) (hinj : Function.Injective ξ) (hcod : ∀ i, Order.coheight (ξ i) = 1)
    (hgen : ∀ i, IsGenericPoint (ξ i) ((D.component i).support : Set X))
    (havoid : ∀ i, ξ i ∉ Z.support)
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i) :
    let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
    let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
    let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
    let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
    let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
    let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
      smoothOfRelativeDimension_blowUpπ_comp (X ↘ Spec (.of k)) n r Z hrn
    let hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := k) Z.blowUpπ) :=
      blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη
    ∀ (c₀ : EtaleChart k X n) (cT₀ : EtaleChart k Z.blowUp n),
    ∃ (ξ' : D.ι → Z.blowUp) (G : D.ι → CartierDivisor Z.blowUp)
      (E : CartierDivisor Z.blowUp) (η : Z.blowUp),
      ∃ (hG : ∀ i, (G i).IsEffective) (hE : E.IsEffective),
        Order.coheight η = 1 ∧
        IsGenericPoint η (Z.exceptionalDivisor.support : Set Z.blowUp) ∧
        Function.Injective ξ' ∧
        (∀ i, Z.blowUpπ (ξ' i) = ξ i) ∧
        (∀ i, Order.coheight (ξ' i) = 1) ∧
        (∀ i, IsGenericPoint (ξ' i) (((D.component i).strictTransform Z).support : Set Z.blowUp)) ∧
        (∀ i, effectiveCartierIdealSheaf (G i) (hG i) = (D.component i).strictTransform Z) ∧
        effectiveCartierIdealSheaf E hE = Z.exceptionalDivisor ∧
        (∀ i, cartierPullback Z.blowUpπ (P i) = G i + if D.component i ≤ Z then E else 0) ∧
        (∀ i (t : CodimensionOnePoint Z.blowUp),
          cartierCoefficient (G i) (t : Z.blowUp) = if (t : Z.blowUp) = ξ' i then 1 else 0) ∧
        (∀ t : CodimensionOnePoint Z.blowUp, cartierCoefficient E (t : Z.blowUp) =
          if (t : Z.blowUp) = η then 1 else 0) ∧
        (∀ i, ξ' i ≠ η) ∧
        (∀ i (t : CodimensionOnePoint X),
          cartierCoefficient (P i) (t : X) = if (t : X) = ξ i then 1 else 0) ∧
        birationalRelativeCanonicalDivisor n Z.blowUpπ hπ c₀ etaleCharts_cover cT₀ etaleCharts_cover =
          (r - 1) • E := by
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    smoothOfRelativeDimension_blowUpπ_comp (X ↘ Spec (.of k)) n r Z hrn
  have hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := k) Z.blowUpπ) :=
    blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη
  dsimp only
  intro c₀ cT₀
  obtain ⟨ξ', G, E, η, hG, hE, hηcod, hηgen, hinj', hπ', hcod', hgen', hGI, hEI,
    hPG, hGc, hEc, hdisj, hPc⟩ :=
    snc_connectedCentre_exists_full_cartier_prime_data (X ↘ Spec (.of k)) n r D Z hD hZ
      hrn hr hη ξ hinj hcod hgen havoid P hP hPI
  refine ⟨ξ', G, E, η, hG, hE, hηcod, hηgen, hinj', hπ', hcod', hgen', hGI, hEI,
    hPG, hGc, hEc, hdisj, hPc, ?_⟩
  exact snc_blowUp_relativeCanonical_eq_nsmul D Z hD hZ hrn E hE hEI
    c₀ etaleCharts_cover cT₀ etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective Z.blowUpπ hπ c₀ cT₀)

end MixedFujita
