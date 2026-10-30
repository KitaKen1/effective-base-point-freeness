/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCSequenceSupportAtlas

/-! The library-selected principalization comes with one prime SNC atlas
supporting both the crepant boundary and the inverse image of the principalized
ideal. This supplies the support data needed by nef-and-big perturbation. -/

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

/-- The inverse image of the ideal principalized by BMO₁ lies in the
ordinary terminal total boundary, by the exact exceptional-product formula. -/
theorem sncMarkedPrincipalizationSequence_support_le_total_boundary
    {k : Type u} [Field k] [CharZero k] (T : Triple k) :
    let S := sncMarkedPrincipalizationSequence T
    (T.I.comap S.composite).support ≤ (S.totalTransformSeq T.E (Fin.last _)).support := by
  let S := sncMarkedPrincipalizationSequence T
  have heq : T.I.comap S.composite = ∏ j : Fin S.length,
      (S.exceptionalAt j).comap (S.stageMapBetween (Fin.last _) j.succ (Fin.le_last _)) :=
    BMO_one_comap_composite_eq_prod (⟨T, 1⟩ : MarkedTriple k) ⟨le_rfl, rfl⟩
  change (T.I.comap S.composite).support ≤ _
  rw [heq, support_finset_prod]
  refine iSup₂_le fun j _ => IsConcreteLE.le_iff.mpr fun t ht => ?_
  rw [mem_support_comap_iff_apply] at ht
  exact preimage_stageMapBetween_support_subset S T.E (Fin.le_last _)
    (support_exceptionalAt_le_support_totalTransformSeq S T.E j ht)

/-- The same principalization and cohomology comparison as before, now with
one finite prime SNC atlas controlling the boundary and the pulled-back ideal.
Off this atlas the composite is a stalk isomorphism and its image avoids both
original supports. No compatibility of independently chosen atlases is assumed. -/
theorem snc_principalization_exists_supported_cohomology_descent
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
      (∃ (r : ℕ) (ξ : Fin r → S.last), Function.Injective ξ ∧
        (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily k n ξ ∧
        (∀ t : CodimensionOnePoint S.last, (t : S.last) ∈ Set.range ξ ↔
          (t : S.last) ∈ (S.totalTransformSeq T.E (Fin.last _)).support) ∧
        ∀ t : CodimensionOnePoint S.last, (t : S.last) ∉ Set.range ξ →
          cartierCoefficient (∑ i, b' i • P' i) (t : S.last) = 0 ∧
          S.composite (t : S.last) ∉ T.I.support ∧
          S.composite (t : S.last) ∉ T.E.support ∧
          Function.Bijective (S.composite.stalkMap (t : S.last))) ∧
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
  let S := sncMarkedPrincipalizationSequence T
  obtain ⟨hinv, hsncI, hT, hTover, hTN, hTsmooth, hdom, hover, hπ, cT, F, P', hP', b',
      hPI', hF, hB, hb, hround, hseq⟩ :=
    snc_principalization_exists_cohomology_descent T n P hP hPI b d hd c₀
  let : IsIntegral S.last := hT
  let : S.last.Over (Spec (.of k)) := hTover
  let : IsNoetherian S.last := hTN
  let : SmoothOfRelativeDimension n (S.last ↘ Spec (.of k)) := hTsmooth
  let : IsDominant S.composite := hdom
  let : S.composite.IsOver (Spec (.of k)) := hover
  let : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  have hS := sncMarkedPrincipalizationSequence_isOrderGeSeq T
  have htotal := IsOrderGeSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) n
    hS T.isSnc (Fin.last _)
  obtain ⟨r, ξ, hinj, hξ, hsnc, hatlas⟩ :=
    sncFamily_exists_prime_support_atlas (k := k) (X := S.last) n
    (S.totalTransformSeq T.E (Fin.last _)) htotal
  refine ⟨hinv, hsncI, hT, hTover, hTN, hTsmooth, hdom, hover, hπ, cT, F, P', hP', b',
    hPI', hF, hB, hb, hround, ⟨r, ξ, hinj, hξ, hsnc, hatlas, ?_⟩, hseq⟩
  intro t ht
  have hnot : (t : S.last) ∉ (S.totalTransformSeq T.E (Fin.last _)).support :=
    fun h => ht ((hatlas t).mpr h)
  obtain ⟨hiso, hnotE⟩ := snc_sequence_stalkIso_off_total_boundary S T.E t hnot
  let := hiso
  refine ⟨?_, ?_, hnotE, ConcreteCategory.bijective_of_isIso _⟩
  · rw [hB]
    apply snc_sequence_crepant_boundary_supported n S hπ c₀ cT T.E _ d ?_ t hnot
    exact snc_cartier_combination_supported (T.X.left ↘ Spec (.of k)) T.E T.isSnc
      P hP hPI b
  · intro hi
    exact hnot (sncMarkedPrincipalizationSequence_support_le_total_boundary T
      ((mem_support_comap_iff_apply T.I S.composite t).mpr hi))

end MixedFujita
