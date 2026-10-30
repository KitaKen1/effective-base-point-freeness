/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCSupportIntrinsicRoundup
public import MixedFujita.SNCComponentRoundupVanishing
public import MixedFujita.BoundedExceptionalCorrectionPushforward
public import MixedFujita.AcyclicPushforwardComposition

/-! Relative vanishing and ordinary pushforward for SNC support roundups.
No boundary generic points, irreducibility, or avoidance of the centre are
assumed. Smooth disconnected boundary members and centres of varying component
codimension are retained, including a centre that is a boundary component. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem snc_support_exists_intrinsic_roundup_pushforward_comparison
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
    ∃ (c : Z.componentFamily.ι → ℕ) (E : Z.componentFamily.ι → CartierDivisor Z.blowUp)
      (hE : ∀ j, (E j).IsEffective),
      (∀ j, 0 < c j ∧ c j ≤ n ∧ SmoothOfRelativeDimension (n - c j)
        ((Z.componentFamily.component j).subschemeι ≫ (X ↘ Spec (.of k)))) ∧
      (∀ j, effectiveCartierIdealSheaf (E j) (hE j) =
        (Z.componentFamily.component j).comap Z.blowUpπ) ∧
      ∀ (c₀ : EtaleChart k X n) (cT₀ : EtaleChart k Z.blowUp n),
      birationalRelativeCanonicalDivisor n Z.blowUpπ hπ c₀ etaleCharts_cover cT₀ etaleCharts_cover =
        ∑ j, (c j - 1) • E j ∧
      ∀ (m : ℕ) (a : Fin m ↪ D.ι) (b : Fin m → ℤ) (d : ℕ), 1 ≤ d →
        let Q := ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P (a i)
        (∀ t : CodimensionOnePoint X, cartierCoefficient Q (t : X) =
          ⌈-((cartierCoefficient (∑ i, b i • P (a i)) (t : X) : ℝ) / (d : ℝ))⌉) ∧
        ∃ (C : CartierDivisor Z.blowUp) (j : Z.componentFamily.ι → ℕ),
          (∀ i, j i ≤ c i - 1) ∧
          (∀ t : CodimensionOnePoint Z.blowUp, cartierCoefficient C (t : Z.blowUp) =
            ⌈-((cartierCoefficient
              (cartierPullback Z.blowUpπ (∑ i, b i • P (a i)) - (d : ℤ) •
                birationalRelativeCanonicalDivisor n Z.blowUpπ hπ
                  c₀ etaleCharts_cover cT₀ etaleCharts_cover) (t : Z.blowUp) : ℝ) / (d : ℝ))⌉) ∧
          C = cartierPullback Z.blowUpπ Q + ∑ i, j i • E i ∧
          (∀ (U : X.Opens), IsAffineOpen U → ∀ q : ℕ,
            Subsingleton (C.sheaf.H' (q + 1) (Z.blowUpπ ⁻¹ᵁ U))) ∧
          (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage Z.blowUpπ C.sheaf (q + 1))) ∧
          Nonempty (Q.sheaf ≅ (Scheme.Modules.pushforward Z.blowUpπ).obj C.sheaf) ∧
          (∀ (U : X.Opens), IsCompact (U : Set X) → ∀ p : ℕ,
            Nonempty (C.sheaf.H' p (Z.blowUpπ ⁻¹ᵁ U) ≃+ Q.sheaf.H' p U)) ∧
          (∀ (B : Scheme.{u}) (g : X ⟶ B) [QuasiCompact g],
            (∀ U : B.Opens, IsAffineOpen U → ∀ q : ℕ,
              Subsingleton (Q.sheaf.H' (q + 1) (g ⁻¹ᵁ U))) →
            (∀ U : B.Opens, IsAffineOpen U → ∀ q : ℕ,
              Subsingleton (C.sheaf.H' (q + 1) ((Z.blowUpπ ≫ g) ⁻¹ᵁ U))) ∧
            (∀ q : ℕ, Limits.IsZero
              (cohomologicalDirectImage (Z.blowUpπ ≫ g) C.sheaf (q + 1)))) := by
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (Z.blowUp ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  have hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := k) x
  have hnormT : ∀ t : Z.blowUp, IsIntegrallyClosed (Z.blowUp.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := k) t
  let hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := k) Z.blowUpπ) :=
    blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη
  dsimp only
  obtain ⟨c, E, hE, hc, hEI, hdata⟩ :=
    snc_support_exists_intrinsic_roundup_with_dimensions (k := k)
      n D Z hD hZ hη P hP hPI
  refine ⟨c, E, hE, hc, hEI, ?_⟩
  intro c₀ cT₀
  obtain ⟨hR, hb⟩ := hdata c₀ cT₀
  refine ⟨hR, ?_⟩
  have hzero : ∀ t : CodimensionOnePoint Z.blowUp,
      Order.coheight (Z.blowUpπ (t : Z.blowUp)) = 1 →
      cartierCoefficient (∑ i, (c i - 1) • E i) (t : Z.blowUp) = 0 := by
    intro t ht
    rw [← hR]
    exact relativeCanonical_coefficient_zero_over_normal_prime Z.blowUpπ hπ hnormX hnormT
      c₀ etaleCharts_cover cT₀ etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective Z.blowUpπ hπ c₀ cT₀) t ht
  intro m a b d hd
  obtain ⟨hQ, C, j, hj, hCc, hC⟩ := hb m a b d hd
  obtain ⟨hv, hz⟩ := sncCentre_component_correction_relative_vanishing
    (X ↘ Spec (.of k)) n D Z hZ hη c hc E hE hEI
    (fun i => P (a i)) (fun i => hP (a i))
    (fun i => ⌈-((b i : ℝ) / (d : ℝ))⌉) C j hj hC
  obtain ⟨e⟩ := signed_bounded_exceptional_correction_pushforward_iso hnormX hnormT
    Z.blowUpπ hπ (fun i => P (a i)) (fun i => hP (a i))
    (fun i => ⌈-((b i : ℝ) / (d : ℝ))⌉) E hE (fun i => c i - 1) j hj hzero C hC
  let Q := ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P (a i)
  let := Q.isInvertible_sheaf
  let := invertibleModule_isQuasicoherent Q.sheaf
  refine ⟨hQ, C, j, hj, hCc, hC, hv, hz, ⟨e⟩, ?_, ?_⟩
  · intro U hU p
    exact ⟨acyclicPushforwardIsoCompactOpenAddEquiv Z.blowUpπ C.sheaf Q.sheaf e hv U hU p⟩
  · intro B g _ hg
    exact affine_relative_vanishing_comp_of_pushforward_iso Z.blowUpπ g C.sheaf Q.sheaf e hv hg

end MixedFujita
