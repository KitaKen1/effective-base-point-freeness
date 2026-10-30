/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentBoundaryTransform
public import MixedFujita.SNCTwistedRoundupCohomology

/-! Propagate the finite unrounded boundary and its canonical roundup together
with actual cohomology comparison. The next boundary is constructed from SNC
geometry; neither its transformation rule nor relative acyclicity is an input.
Compatibility with the next centre is inherited from the ordinary transform.
Global compatibility along an entire resolution remains a separate obligation. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The transformed finite boundary, its canonical roundup and all-degree
comparison are supplied together, ready for the next compatible blow-up. -/
theorem snc_component_boundary_roundup_propagation
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.IsSeparated] [X.Over (Spec (.of k))]
    (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support)
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i) :
    let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
    let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
    let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
    let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
    let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
    let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
      snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
    let hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := k) Z.blowUpπ) :=
      blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη
    let F := sncComponentTotalTransform D Z
    ∃ (c : Z.componentFamily.ι → ℕ) (P' : F.ι → CartierDivisor Z.blowUp)
      (hP' : ∀ i, (P' i).IsEffective),
      (∀ i, effectiveCartierIdealSheaf (P' i) (hP' i) = F.component i) ∧
      F.IsSnc ∧
      (∀ W, (D.totalTransform Z).HasSncWith W → F.HasSncWith W) ∧
      ∀ (c₀ : EtaleChart k X n) (cT₀ : EtaleChart k Z.blowUp n)
        (b : D.ι → ℤ) (d : ℕ), 1 ≤ d →
        let b' := sncComponentBoundaryCoefficients D Z c b d
        let Q := ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i
        let C := ∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i
        (∑ i, b' i • P' i = cartierPullback Z.blowUpπ (∑ i, b i • P i) - (d : ℤ) •
          birationalRelativeCanonicalDivisor n Z.blowUpπ hπ
            c₀ etaleCharts_cover cT₀ etaleCharts_cover) ∧
        (∀ t : CodimensionOnePoint Z.blowUp, cartierCoefficient C (t : Z.blowUp) =
          ⌈-((cartierCoefficient (∑ i, b' i • P' i) (t : Z.blowUp) : ℝ) / (d : ℝ))⌉) ∧
        ((∀ i, b i < (d : ℤ)) → ∀ i, b' i < (d : ℤ)) ∧
        ∀ A : CartierDivisor X,
          Nonempty ((A + Q).sheaf ≅ (Scheme.Modules.pushforward Z.blowUpπ).obj
            (cartierPullback Z.blowUpπ A + C).sheaf) ∧
          (∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
            Subsingleton ((cartierPullback Z.blowUpπ A + C).sheaf.H' (q + 1)
              (Z.blowUpπ ⁻¹ᵁ U))) ∧
          (∀ j : ℕ, Nonempty
            (Scheme.Modules.Cohomology (cartierPullback Z.blowUpπ A + C).sheaf j ≃+
              Scheme.Modules.Cohomology (A + Q).sheaf j)) ∧
          (∀ (rest : BlowUpSequence Z.blowUp) (N : rest.last.Modules),
            blowUpSequenceAcyclicModules rest (cartierPullback Z.blowUpπ A + C).sheaf N →
            blowUpSequenceAcyclicModules (.cons X Z rest) (A + Q).sheaf N) := by
  classical
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (Z.blowUp ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  dsimp only
  obtain ⟨c, P', hP', hc, hPI', hF, hnext, hB⟩ :=
    snc_component_crepant_boundary_transform (k := k) n D Z hD hZ hη P hP hPI
  refine ⟨c, P', hP', hPI', hF, hnext, ?_⟩
  intro c₀ cT₀ b d hd
  let b' := sncComponentBoundaryCoefficients D Z c b d
  let Q := ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i
  let C := ∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i
  have hQ := snc_cartier_roundup_family_coefficient
    (X ↘ Spec (.of k)) D hD P hP hPI b d
  have hC := snc_cartier_roundup_family_coefficient
    (Z.blowUp ↘ Spec (.of k)) _ hF P' hP' hPI' b' d
  refine ⟨hB c₀ cT₀ b d, hC, ?_, ?_⟩
  · exact snc_component_boundary_coefficients_lt_denominator
      (X ↘ Spec (.of k)) n D Z hZ c hc b d hd
  intro A
  let e := (Fintype.equivFin D.ι).symm
  have hs : (∑ i, b (e i) • P (e i)) = ∑ i, b i • P i :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  apply snc_support_roundup_twisted_cohomology_comparison
    (k := k) n D Z hD hZ hη P hP hPI c₀ cT₀
    (Fintype.card D.ι) e.toEmbedding (b ∘ e) d hd Q C
  · intro t
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, hs] using hQ t
  · intro t
    have h := hC t
    change cartierCoefficient C (t : Z.blowUp) =
      ⌈-((cartierCoefficient (∑ i, sncComponentBoundaryCoefficients D Z c b d i • P' i)
        (t : Z.blowUp) : ℝ) / (d : ℝ))⌉ at h
    rw [hB c₀ cT₀ b d] at h
    simpa only [Function.comp_apply, Equiv.toEmbedding_apply, hs] using h

end MixedFujita
