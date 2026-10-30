/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ConnectedRegularCentre
public import MixedFujita.SNCStrictTransformPrimes
public import MixedFujita.SNCStrictTransformCartier

/-! Actual strict-transform prime data from a connected SNC center and original
prime components. Uniform incidence, target prime points and total-transform
identities are constructed internally. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem snc_connectedCentre_exists_cartier_prime_data
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
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
    ∃ (ξ' : D.ι → Z.blowUp) (G : D.ι → CartierDivisor Z.blowUp)
      (E : CartierDivisor Z.blowUp),
      ∃ (hG : ∀ i, (G i).IsEffective) (hE : E.IsEffective),
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
          if (t : Z.blowUp) ∈ Z.exceptionalDivisor.support then 1 else 0) ∧
        (∀ i (η : Z.blowUp), η ∈ Z.exceptionalDivisor.support → ξ' i ≠ η) ∧
        (∀ i (t : CodimensionOnePoint X),
          cartierCoefficient (P i) (t : X) = if (t : X) = ξ i then 1 else 0) := by
  let := snc_connectedCentre_isIntegral f D Z hZ
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  obtain ⟨G, E, hG, hE, hGI, hEI, hPG, _, hEc⟩ :=
    snc_exists_strictTransform_cartier_totalTransform f D Z hD hZ hη
      (fun i => D.component i ≤ Z)
      (fun i x hx => integralSubscheme_stalkIdeal_le_iff (D.component i) Z x hx) P hP hPI
  obtain ⟨ξ', hinj', hπ, hcod', hgen', hGc, hdisj⟩ :=
    snc_exists_strictTransform_primeProfiles f D Z hD hZ ξ hinj hcod hgen havoid G hG hGI
  exact ⟨ξ', G, E, hG, hE, hinj', hπ, hcod', hgen', hGI, hEI, hPG, hGc, hEc, hdisj,
    fun i => snc_source_cartier_primeProfile f D hD i (ξ i) (hcod i) (hgen i)
      (P i) (hP i) (hPI i)⟩

end MixedFujita
