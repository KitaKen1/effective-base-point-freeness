/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCSmoothDivisorCoefficients
public import MixedFujita.HironakaPrincipalizingRound
public import MixedFujita.BirationalPrimeLifts
public import MixedFujita.CartierSectionSNCPerturbation
public import Hironaka.Scheme.BlowUpSequence.StrictTransformIntegral
public import Hironaka.Scheme.BlowUp.Glue.Trivial
public import Hironaka.Scheme.Snc.Family
public import Hironaka.Algebra.RegularSmooth.SchemeForms

/-! Construct the distinct codimension-one generic points of actual strict transforms
by lifting the original generic points through the isomorphism off the center. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem exists_strictTransform_prime_lifts
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (ξ : D.ι → X)
    (hinj : Function.Injective ξ) (hcod : ∀ i, Order.coheight (ξ i) = 1)
    (hgen : ∀ i, IsGenericPoint (ξ i) ((D.component i).support : Set X))
    (havoid : ∀ i, ξ i ∉ Z.support) :
    ∃ ξ' : D.ι → Z.blowUp, Function.Injective ξ' ∧
      (∀ i, Z.blowUpπ (ξ' i) = ξ i) ∧
      (∀ i, Order.coheight (ξ' i) = 1) ∧
      (∀ i, IsGenericPoint (ξ' i) (((D.component i).strictTransform Z).support : Set Z.blowUp)) ∧
      (∀ i, ξ' i ∉ Z.exceptionalDivisor.support) := by
  choose ξ' hξ' using fun i => exists_π_eq_of_notMem_support Z (havoid i)
  have hoff : ∀ i, Z.blowUpπ (ξ' i) ∉ Z.support := fun i => by rw [hξ' i]; exact havoid i
  refine ⟨ξ', ?_, hξ', ?_, ?_, ?_⟩
  · intro i j h
    apply hinj
    rw [← hξ' i, ← hξ' j, h]
  · intro i
    let := blowUp_isIso_stalkMap_of_notMem_support Z (ξ' i) (hoff i)
    rw [coheight_eq_of_stalkMap_bijective Z.blowUpπ (ξ' i)
      (ConcreteCategory.bijective_of_isIso (Z.blowUpπ.stalkMap (ξ' i))), hξ' i, hcod i]
  · exact fun i => isGenericPoint_strictTransform Z (D.component i) (hgen i) (havoid i) (hξ' i)
  · intro i hi
    exact hoff i ((mem_support_comap_iff_apply Z Z.blowUpπ (ξ' i)).mp hi)

theorem cartier_primeProfile_of_generic_support
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) (G : CartierDivisor Y) (ξ : Y)
    (hcod : Order.coheight ξ = 1) (hgen : IsGenericPoint ξ (I.support : Set Y))
    (hcoeff : ∀ t : CodimensionOnePoint Y,
      cartierCoefficient G (t : Y) = if (t : Y) ∈ I.support then 1 else 0) :
    ∀ t : CodimensionOnePoint Y,
      cartierCoefficient G (t : Y) = if (t : Y) = ξ then 1 else 0 := by
  intro t
  rw [hcoeff]
  have hmem : (t : Y) ∈ I.support ↔ (t : Y) = ξ := by
    rw [← SetLike.mem_coe, ← hgen.def]
    exact scheme_codimensionOne_mem_closure_iff_eq (t : Y) ξ t.property hcod
  rw [hmem]

theorem snc_source_cartier_primeProfile
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (D : DivisorFamily X) (hD : D.IsSnc)
    (i : D.ι) (ξ : X) (hcod : Order.coheight ξ = 1)
    (hgen : IsGenericPoint ξ ((D.component i).support : Set X))
    (P : CartierDivisor X) (hP : P.IsEffective)
    (hPI : effectiveCartierIdealSheaf P hP = D.component i) :
    ∀ t : CodimensionOnePoint X,
      cartierCoefficient P (t : X) = if (t : X) = ξ then 1 else 0 := by
  apply cartier_primeProfile_of_generic_support (D.component i) P ξ hcod hgen
  intro t
  let := isRegularLocalRing_stalk f (t : X)
  let : IsDiscreteValuationRing (X.presheaf.stalk (t : X)) := inferInstance
  exact smoothDivisor_cartierCoefficient (D.component i)
    (isSmoothDivisor_of_snc_data D.component hD.1 (isSnc_data D hD)
      (fun x => isRegularLocalRing_stalk f x) i) P hP hPI t

theorem snc_exists_strictTransform_primeProfiles
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp]
    (ξ : D.ι → X) (hinj : Function.Injective ξ) (hcod : ∀ i, Order.coheight (ξ i) = 1)
    (hgen : ∀ i, IsGenericPoint (ξ i) ((D.component i).support : Set X))
    (havoid : ∀ i, ξ i ∉ Z.support)
    (G : D.ι → CartierDivisor Z.blowUp) (hG : ∀ i, (G i).IsEffective)
    (hGI : ∀ i, effectiveCartierIdealSheaf (G i) (hG i) = (D.component i).strictTransform Z) :
    ∃ ξ' : D.ι → Z.blowUp, Function.Injective ξ' ∧
      (∀ i, Z.blowUpπ (ξ' i) = ξ i) ∧
      (∀ i, Order.coheight (ξ' i) = 1) ∧
      (∀ i, IsGenericPoint (ξ' i) (((D.component i).strictTransform Z).support : Set Z.blowUp)) ∧
      (∀ i (t : CodimensionOnePoint Z.blowUp),
        cartierCoefficient (G i) (t : Z.blowUp) = if (t : Z.blowUp) = ξ' i then 1 else 0) ∧
      (∀ i (η : Z.blowUp), η ∈ Z.exceptionalDivisor.support → ξ' i ≠ η) := by
  obtain ⟨ξ', hinj', hπ, hcod', hgen', hoff⟩ :=
    exists_strictTransform_prime_lifts D Z ξ hinj hcod hgen havoid
  refine ⟨ξ', hinj', hπ, hcod', hgen', ?_, ?_⟩
  · intro i
    apply cartier_primeProfile_of_generic_support _ (G i) (ξ' i) (hcod' i) (hgen' i)
    exact snc_totalTransform_cartierCoefficient f D Z hD hZ (toLex (Sum.inl i))
      (G i) (hG i) (hGI i)
  · intro i η hη heq
    exact hoff i (heq ▸ hη)

end MixedFujita
