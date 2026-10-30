/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCPrincipalizationCohomology
public import MixedFujita.HironakaSNCDictionary
public import MixedFujita.HironakaBlowUpModels
public import MixedFujita.LocalBirationalOrders
public import Hironaka.Resolution.Algebraic.Kol07.OffCenters
public import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary

/-! A common prime-divisor atlas for a total SNC transform. Away from it,
all stalk maps are isomorphisms and the relative canonical coefficient is zero.
These statements do not require identifying the component-split boundary
chosen by the cohomology construction with the ordinary total transform. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open Hironaka.Sequence
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- A finite SNC family has a finite prime-divisor atlas covering precisely
its codimension-one support, even when the original members are disconnected. -/
theorem sncFamily_exists_prime_support_atlas
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.Over (Spec (.of k))]
    (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (D : DivisorFamily X) (hD : D.IsSnc) :
    ∃ (r : ℕ) (ξ : Fin r → X), Function.Injective ξ ∧
      (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily k n ξ ∧
      ∀ t : CodimensionOnePoint X, (t : X) ∈ Set.range ξ ↔ (t : X) ∈ D.support := by
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let E := D.unionIdeal
  have hE : E.IsSncBoundary := IsSnc.isSncBoundary_unionIdeal (X ↘ Spec (.of k)) hD
  let e : Fin (Nat.card E.support.genericPoints) ≃ E.support.genericPoints :=
    (Finite.equivFin _).symm
  let ξ : Fin (Nat.card E.support.genericPoints) → X := fun i => (e i).1
  have hinj : Function.Injective ξ := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ i, ξ i ∈ E.support.genericPoints := fun i => (e i).2
  have hcoh : ∀ η ∈ E.support.genericPoints, Order.coheight η = 1 :=
    fun η hη => coheight_eq_one_of_mem_genericPoints_of_isSncBoundary E hE hη
  refine ⟨_, ξ, hinj, fun i => hcoh _ (hmem i),
    isSNCFamily_of_isSncBoundary E hE ξ hinj hmem, ?_⟩
  intro t
  have hs : E.support = D.support := Closeds.ext (by simp [E, DivisorFamily.unionIdeal])
  rw [← hs]
  constructor
  · rintro ⟨i, hi⟩
    rw [← hi]
    exact (hmem i).1
  · intro ht
    obtain ⟨η, hη, hηt⟩ := Closeds.exists_mem_genericPoints_specializes E.support ht
    have heq : (⟨η, hcoh η hη⟩ : CodimensionOnePoint X) = t :=
      CodimensionOnePoint.eq_of_specializes (x := t) (y := ⟨η, hcoh η hη⟩) hηt
    refine ⟨e.symm ⟨η, hη⟩, ?_⟩
    change (e (e.symm ⟨η, hη⟩)).1 = (t : X)
    rw [Equiv.apply_symm_apply]
    exact congrArg Subtype.val heq

/-- Outside the terminal total boundary a sequence is an isomorphism on stalks,
and its image is outside the original boundary. -/
theorem snc_sequence_stalkIso_off_total_boundary
    {X : Scheme.{u}} [IsLocallyNoetherian X] (S : BlowUpSequence X)
    (D : DivisorFamily X) (t : S.last)
    (ht : t ∉ (S.totalTransformSeq D (Fin.last _)).support) :
    IsIso (S.composite.stalkMap t) ∧ S.composite t ∉ D.support := by
  have h := mem_support_totalTransformSeq_iff S D (Fin.last _) t
  refine ⟨isIso_stalkMap_stageMap_of_forall_notMem S (Fin.last _) t ?_, ?_⟩
  · intro i hi hmem
    exact ht (h.mpr (Or.inr ⟨i, hi, hmem⟩))
  · intro hmem
    exact ht (h.mpr (Or.inl hmem))

/-- Integer combinations of the Cartier members vanish off the family support. -/
theorem snc_cartier_combination_supported
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (D : DivisorFamily X) (hD : D.IsSnc)
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i)
    (b : D.ι → ℤ) (t : CodimensionOnePoint X) (ht : (t : X) ∉ D.support) :
    cartierCoefficient (∑ i, b i • P i) (t : X) = 0 := by
  rw [cartierCoefficient_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hi : (t : X) ∉ (D.component i).support :=
    fun hi => ht ((DivisorFamily.mem_support_iff_exists D _).mpr ⟨i, hi⟩)
  rw [cartierCoefficient_zsmul, snc_cartier_support_profile f D hD i (P i) (hP i) (hPI i),
    ite_eq_right hi, mul_zero]

/-- The crepant transform of a divisor supported on the original boundary
is supported on the ordinary total boundary of any blow-up sequence. -/
theorem snc_sequence_crepant_boundary_supported
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [X.Over (Spec (.of k))] (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (S : BlowUpSequence X) [IsIntegral S.last] [IsNoetherian S.last]
    [S.last.Over (Spec (.of k))]
    [SmoothOfRelativeDimension n (S.last ↘ Spec (.of k))]
    [IsDominant S.composite] [S.composite.IsOver (Spec (.of k))]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := k) S.composite))
    (c₀ : EtaleChart k X n) (cT : EtaleChart k S.last n)
    (D : DivisorFamily X) (B : CartierDivisor X) (d : ℕ)
    (hsupp : ∀ x : CodimensionOnePoint X, (x : X) ∉ D.support →
      cartierCoefficient B (x : X) = 0)
    (t : CodimensionOnePoint S.last)
    (ht : (t : S.last) ∉ (S.totalTransformSeq D (Fin.last _)).support) :
    cartierCoefficient (cartierPullback S.composite B - (d : ℤ) •
      birationalRelativeCanonicalDivisor n S.composite hπ
        c₀ etaleCharts_cover cT etaleCharts_cover) (t : S.last) = 0 := by
  obtain ⟨hiso, hnot⟩ := snc_sequence_stalkIso_off_total_boundary S D t ht
  let := hiso
  have hbij : Function.Bijective (S.composite.stalkMap (t : S.last)) :=
    ConcreteCategory.bijective_of_isIso _
  have hcoh : Order.coheight (S.composite (t : S.last)) = 1 := by
    rw [← coheight_eq_of_stalkMap_bijective S.composite (t : S.last) hbij]
    exact t.property
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (S.last ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := k) t
  let := smoothOverField_codimensionOne_stalk_DVR (K := k)
    (⟨S.composite (t : S.last), hcoh⟩ : CodimensionOnePoint X)
  have hK : cartierCoefficient (birationalRelativeCanonicalDivisor n S.composite hπ
      c₀ etaleCharts_cover cT etaleCharts_cover) (t : S.last) = 0 :=
    relativeCanonical_coefficient_zero_of_stalkMap_bijective S.composite
      c₀ etaleCharts_cover cT etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective S.composite hπ c₀ cT) t hbij
  rw [cartierCoefficient_sub, cartierCoefficient_zsmul, hK, mul_zero, sub_zero,
    cartierCoefficient_pullback_of_stalkMap_bijective S.composite t hcoh hbij]
  exact hsupp ⟨_, hcoh⟩ hnot

end MixedFujita
