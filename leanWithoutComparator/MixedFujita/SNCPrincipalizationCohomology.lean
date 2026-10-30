/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCMarkedOrderSequenceCohomology
public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Principalization.Monomial
public import Hironaka.Resolution.Algebraic.Kol07.ExceptionalMonomial
public import Hironaka.Resolution.Algebraic.Stage.DimFreeTheorems
public import Hironaka.Resolution.Algebraic.Snc.SncInvertible
public import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
public import Hironaka.Resolution.Algebraic.Kol07.IsoRestrict
public import Hironaka.Scheme.BlowUpSequence.Projective

/-! A concrete principalization with crepant-roundup cohomology descent.
Kollár's marked order-reduction functor at mark one provides the sequence;
no admissible sequence or stepwise vanishing is supplied as an extra input.
This applies to a smooth SNC triple, not to an initial singular klt model. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open Hironaka Hironaka.Stage Hironaka.Sequence
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The actual marked order-reduction sequence at mark one for a smooth SNC triple. -/
noncomputable def sncMarkedPrincipalizationSequence
    {k : Type u} [Field k] [CharZero k] (T : Triple k) : BlowUpSequence T.X.left :=
  (BMO_m 1 k).seq ⟨T, 1⟩ ⟨le_rfl, rfl⟩

/-- The selected sequence retains all centre-admissibility clauses needed for descent. -/
theorem sncMarkedPrincipalizationSequence_isOrderGeSeq
    {k : Type u} [Field k] [CharZero k] (T : Triple k) :
    (sncMarkedPrincipalizationSequence T).IsOrderGeSeq
      (T.X.left ↘ Spec (.of k)) T.I 1 T.E :=
  (BMO_m 1 k).isOrderGeSeq ⟨T, 1⟩ ⟨le_rfl, rfl⟩

/-- At mark one, order reduction ends at the unit marked transform. -/
theorem sncMarkedPrincipalizationSequence_markedTransform_eq_top
    {k : Type u} [Field k] [CharZero k] (T : Triple k) :
    (sncMarkedPrincipalizationSequence T).markedTransformSeq T.I 1 (Fin.last _) = ⊤ := by
  have h1 : ((sncMarkedPrincipalizationSequence T).markedTransformSeq T.I 1
      (Fin.last _)).maxOrd < 1 := by
    have h := dimFreeBMO_maxOrd_lt stage0 1 (⟨T, 1⟩ : MarkedTriple k) ⟨le_rfl, rfl⟩
    rw [Nat.cast_one] at h
    exact h
  exact Hironaka.BD.eq_top_of_maxOrd_le_zero _
    ((Order.lt_one_iff.mp h1).le.trans Nat.cast_zero.symm.le)

/-- This same sequence principalizes the original ideal as an invertible SNC ideal. -/
theorem sncMarkedPrincipalizationSequence_principalizes
    {k : Type u} [Field k] [CharZero k] (T : Triple k) :
    (T.I.comap (sncMarkedPrincipalizationSequence T).composite).IsInvertible ∧
      IsIdealOfSncDivisor (T.I.comap (sncMarkedPrincipalizationSequence T).composite) := by
  let S := sncMarkedPrincipalizationSequence T
  have hS := sncMarkedPrincipalizationSequence_isOrderGeSeq T
  have heq : T.I.comap S.composite = ∏ j : Fin S.length,
      (S.exceptionalAt j).comap (S.stageMapBetween (Fin.last _) j.succ (Fin.le_last _)) :=
    BMO_one_comap_composite_eq_prod (⟨T, 1⟩ : MarkedTriple k) ⟨le_rfl, rfl⟩
  have hsnc : IsIdealOfSncDivisor (T.I.comap S.composite) := by
    rw [heq]
    exact isIdealOfSncDivisor_prod_comap_exceptionalAt ⟨T, 1⟩ S hS
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  let : Smooth (S.composite ≫ (T.X.left ↘ Spec (.of k))) :=
    IsSmooth.smooth_stageMap (n := n) hS.1 (Fin.last _)
  exact ⟨hsnc.isInvertible (S.composite ≫ (T.X.left ↘ Spec (.of k))), hsnc⟩

/-- The chosen principalization is projective, and is unchanged off the
support of the original ideal. All of its centres lie over that support. -/
theorem sncMarkedPrincipalizationSequence_geometric_control
    {k : Type u} [Field k] [CharZero k] (T : Triple k) :
    let S := sncMarkedPrincipalizationSequence T
    IsProjective S.composite ∧
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ T.I.support) ∧
      IsIso (S.composite ∣_ T.I.support.compl) := by
  let S := sncMarkedPrincipalizationSequence T
  let : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  have hc : ∀ (i : Fin S.length) (z : S.stage i.castSucc),
      z ∈ (S.center i).support → S.stageMap i.castSucc z ∈ T.I.support :=
    fun i _ hz => Hironaka.Resolution.stageMap_mem_support_of_mem_center
      (T.X.left ↘ Spec (.of k)) n
      (sncMarkedPrincipalizationSequence_isOrderGeSeq T) le_rfl i hz
  exact ⟨S.isProjective_composite, hc,
    Hironaka.Sequence.isIso_composite_restrict_of_centers_disjoint S T.I.support.compl
      (fun i => Set.disjoint_left.mpr fun z hz hzU => hzU (hc i z hz))⟩

/-- A library-selected principalization, with the finite crepant boundary,
coefficient bound, affine relative vanishing and all-degree cohomology descent.
The principalizing ideal and the cohomology comparison use exactly the same sequence. -/
theorem snc_principalization_exists_cohomology_descent
    {k : Type u} [Field k] [CharZero k] (T : Triple k) [IsIntegral T.X.left]
    (n : ℕ) [SmoothOfRelativeDimension n (T.X.left ↘ Spec (.of k))]
    (P : T.E.ι → CartierDivisor T.X.left) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = T.E.component i)
    (b : T.E.ι → ℤ) (d : ℕ) (hd : 1 ≤ d) (c₀ : EtaleChart k T.X.left n) :
    let S := sncMarkedPrincipalizationSequence T
    (T.I.comap S.composite).IsInvertible ∧ IsIdealOfSncDivisor (T.I.comap S.composite) ∧
    ∃ (_ : IsIntegral S.last) (_ : S.last.Over (Spec (.of k))) (_ : IsNoetherian S.last)
      (_ : SmoothOfRelativeDimension n (S.last ↘ Spec (.of k)))
      (_ : IsDominant S.composite) (_ : S.composite.IsOver (Spec (.of k)))
      (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := k) S.composite))
      (cT : EtaleChart k S.last n) (F : DivisorFamily S.last)
      (P' : F.ι → CartierDivisor S.last) (hP' : ∀ i, (P' i).IsEffective) (b' : F.ι → ℤ),
      (∀ i, effectiveCartierIdealSheaf (P' i) (hP' i) = F.component i) ∧ F.IsSnc ∧
      (∑ i, b' i • P' i = cartierPullback S.composite (∑ i, b i • P i) - (d : ℤ) •
        birationalRelativeCanonicalDivisor n S.composite hπ
          c₀ etaleCharts_cover cT etaleCharts_cover) ∧
      ((∀ i, b i < (d : ℤ)) → ∀ i, b' i < (d : ℤ)) ∧
      (∀ t : CodimensionOnePoint S.last,
        cartierCoefficient (∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i) (t : S.last) =
          ⌈-((cartierCoefficient (cartierPullback S.composite (∑ i, b i • P i) - (d : ℤ) •
            birationalRelativeCanonicalDivisor n S.composite hπ
              c₀ etaleCharts_cover cT etaleCharts_cover) (t : S.last) : ℝ) / (d : ℝ))⌉) ∧
      ∀ A : CartierDivisor T.X.left,
        let M := (A + ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i).sheaf
        let N := (cartierPullback S.composite A + ∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i).sheaf
        Nonempty (M ≅ (Scheme.Modules.pushforward S.composite).obj N) ∧
        (∀ U : T.X.left.Opens, IsAffineOpen U → ∀ q : ℕ,
          Subsingleton (N.H' (q + 1) (S.composite ⁻¹ᵁ U))) ∧
        (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage S.composite N (q + 1))) ∧
        ∀ j : ℕ, Nonempty (Scheme.Modules.Cohomology N j ≃+ Scheme.Modules.Cohomology M j) ∧
          (Subsingleton (Scheme.Modules.Cohomology N j) ↔
            Subsingleton (Scheme.Modules.Cohomology M j)) := by
  let : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  let : T.X.left.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (T.X.left ↘ Spec (.of k))]
    infer_instance⟩
  obtain ⟨hinv, hsnc⟩ := sncMarkedPrincipalizationSequence_principalizes T
  refine ⟨hinv, hsnc, ?_⟩
  exact snc_orderGeSeq_exists_cohomology_descent n (sncMarkedPrincipalizationSequence T)
    T.I 1 T.isNonzeroEverywhere le_rfl T.E T.isSnc
    (sncMarkedPrincipalizationSequence_isOrderGeSeq T) P hP hPI b d hd c₀

end MixedFujita
