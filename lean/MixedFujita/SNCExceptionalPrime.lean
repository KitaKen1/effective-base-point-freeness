/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothExceptionalIntegral
public import MixedFujita.IntegralCartierPrime
public import MixedFujita.SNCConnectedCentreCartier
public import MixedFujita.SNCStrictTransformPrimes
public import MixedFujita.SNCStrictTransformCartier

/-! Complete strict and exceptional prime profiles for a connected SNC center
of fixed positive codimension. The relative dimensions of the ambient scheme
and center are explicit. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem snc_connectedCentre_exceptional_primeProfile
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n r : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n) (hr : 0 < r)
    [IsNoetherian Z.subscheme] [ConnectedSpace Z.subscheme]
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp]
    (E : CartierDivisor Z.blowUp) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = Z.exceptionalDivisor) :
    ∃ η : Z.blowUp, Order.coheight η = 1 ∧
      IsGenericPoint η (Z.exceptionalDivisor.support : Set Z.blowUp) ∧
      ∀ t : CodimensionOnePoint Z.blowUp,
        cartierCoefficient E (t : Z.blowUp) = if (t : Z.blowUp) = η then 1 else 0 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := snc_connectedCentre_isIntegral f D Z hZ
  let := smoothCentre_exceptional_isIntegral f n r Z hrn hr
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ f⟩
  apply integral_effectiveCartier_exists_primeProfile (K := k) E hE Z.exceptionalDivisor hEI
  intro t
  let := isRegularLocalRing_stalk_blowUp' f D.component Z (hasSncWith_data D Z hZ) (t : Z.blowUp)
  infer_instance

theorem snc_connectedCentre_exists_full_cartier_prime_data
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (n r : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n) (hr : 0 < r)
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
          cartierCoefficient (P i) (t : X) = if (t : X) = ξ i then 1 else 0) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  obtain ⟨ξ', G, E, hG, hE, hinj', hπ, hcod', hgen', hGI, hEI, hPG, hGc, _, hdisj, hPc⟩ :=
    snc_connectedCentre_exists_cartier_prime_data f D Z hD hZ hη ξ hinj hcod hgen havoid P hP hPI
  obtain ⟨η, hηcod, hηgen, hEc⟩ :=
    snc_connectedCentre_exceptional_primeProfile f n r D Z hZ hrn hr E hE hEI
  exact ⟨ξ', G, E, η, hG, hE, hηcod, hηgen, hinj', hπ, hcod', hgen', hGI, hEI,
    hPG, hGc, hEc, fun i => hdisj i η hηgen.mem, hPc⟩

end MixedFujita
