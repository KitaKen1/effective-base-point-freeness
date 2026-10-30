/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCMarkedOrderSequenceRoundup

/-! All-degree cohomology descent through an actual positive marked-order Hironaka
sequence, with the terminal crepant roundup and acyclic sequence constructed
from the original geometric data. No stepwise vanishing is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Global cohomology, affine relative acyclicity and higher direct images are
compared for the geometrically constructed crepant roundup on the final model. -/
theorem snc_orderGeSeq_exists_cohomology_descent
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    [hX : IsIntegral X] [hNX : IsNoetherian X] [hsep : X.IsSeparated]
    [hOver : X.Over (Spec (.of k))] (n : ℕ)
    [hsmooth : SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (S : BlowUpSequence X) (I : X.IdealSheafData) (m : ℕ)
    (hI : IsNonzeroEverywhere I) (hm : 1 ≤ m)
    (D : DivisorFamily X) (hD : D.IsSnc) (hS : S.IsOrderGeSeq (X ↘ Spec (.of k)) I m D)
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i)
    (b : D.ι → ℤ) (d : ℕ) (hd : 1 ≤ d) (c₀ : EtaleChart k X n) :
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
      ∀ A : CartierDivisor X,
        let M := (A + ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i).sheaf
        let N := (cartierPullback S.composite A + ∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i).sheaf
        Nonempty (M ≅ (Scheme.Modules.pushforward S.composite).obj N) ∧
        (∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
          Subsingleton (N.H' (q + 1) (S.composite ⁻¹ᵁ U))) ∧
        (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage S.composite N (q + 1))) ∧
        ∀ j : ℕ, Nonempty (Scheme.Modules.Cohomology N j ≃+ Scheme.Modules.Cohomology M j) ∧
          (Subsingleton (Scheme.Modules.Cohomology N j) ↔
            Subsingleton (Scheme.Modules.Cohomology M j)) := by
  obtain ⟨hT, hTover, hTN, hTsmooth, hdom, hover, hπ, cT, F, P', hP', b',
    hPI', hF, hB, hb, hseq⟩ :=
    snc_orderGeSeq_exists_rounded_boundary_model n S I m hI hm D hD hS P hP hPI b d hd c₀
  let := hT
  let := hTover
  let := hTN
  let := hTsmooth
  let := hdom
  let := hover
  let : Smooth (S.last ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  refine ⟨hT, hTover, hTN, hTsmooth, hdom, hover, hπ, cT, F, P', hP', b',
    hPI', hF, hB, hb, ?_, ?_⟩
  · intro t
    have h := snc_cartier_roundup_family_coefficient
      (S.last ↘ Spec (.of k)) F hF P' hP' hPI' b' d t
    rw [hB] at h
    exact h
  · intro A
    let M := (A + ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i).sheaf
    let N := (cartierPullback S.composite A + ∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i).sheaf
    let := (A + ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i).isInvertible_sheaf
    let := invertibleModule_isQuasicoherent M
    obtain ⟨⟨e⟩, hv, hR⟩ := blowUpSequence_acyclic_pushforward S M N (hseq A)
    refine ⟨⟨e⟩, hv, hR, fun j => ?_⟩
    exact ⟨⟨acyclicPushforwardActualCohomologyAddEquiv S.composite N M e hv j⟩,
      actual_cohomology_subsingleton_iff_of_acyclic_pushforward S.composite N M e hv j⟩

end MixedFujita
