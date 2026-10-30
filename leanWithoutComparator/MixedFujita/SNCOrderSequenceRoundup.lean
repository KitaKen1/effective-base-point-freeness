/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCFamilyRefinementSequence
public import MixedFujita.SNCBoundaryRoundupPropagation
public import MixedFujita.CartierRoundupCompatibility
public import MixedFujita.ThresholdModelLifting

/-! Construct the rounded crepant boundary on the last model of an actual
Hironaka order sequence. Standard geometric order-sequence data supply every
centre, transformed finite boundary, and acyclic pushforward step. -/

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

/-- A positive order sequence of a nowhere-zero ideal never starts by blowing
up the generic point. This is derived from Hironaka's component theorem. -/
theorem snc_orderSeq_genericPoint_notMem_first_center
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (Z : X.IdealSheafData) (rest : BlowUpSequence Z.blowUp)
    (I : X.IdealSheafData) (D : DivisorFamily X) (m : ℕ)
    (hS : (BlowUpSequence.cons X Z rest).IsOrderSeq f I D m)
    (hI : IsNonzeroEverywhere I) (hm : 1 ≤ m) : genericPoint X ∉ Z.support := by
  have hnot := IsOrderSeq.not_component_subset_center f n hS hI hm
    ⟨0, Nat.succ_pos _⟩ Set.univ (by
      change (Set.univ : Set X) ∈ irreducibleComponents X
      simp [irreducibleComponents_eq_singleton])
  intro hη
  apply hnot
  change (Set.univ : Set X) ⊆ Z.support
  rw [← genericPoint_closure X]
  exact closure_minimal (Set.singleton_subset_iff.mpr hη) Z.support.isClosed

/-- The actual relative canonical divisor of the identity vanishes, with
arbitrary reference charts. -/
theorem birationalRelativeCanonicalDivisor_id_eq_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (.of k))] (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (c₀ c₁ : EtaleChart k X n) :
    birationalRelativeCanonicalDivisor n (𝟙 X) dominantFunctionFieldMap_id_bijective
      c₀ etaleCharts_cover c₁ etaleCharts_cover = 0 := by
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  apply cartierDivisor_eq_of_forall_coefficient_eq (fun x => smooth_stalk_isIntegrallyClosed (K := k) x)
  intro t
  let := isRegularLocalRing_stalk (X ↘ Spec (.of k)) (t : X)
  let : IsDiscreteValuationRing (X.presheaf.stalk (t : X)) := inferInstance
  rw [cartierCoefficient_zero]
  exact relativeCanonical_coefficient_zero_of_stalkMap_bijective (𝟙 X)
    c₀ etaleCharts_cover c₁ etaleCharts_cover
    (isUnit_chartRelativeJacobianDet_of_bijective (𝟙 X) dominantFunctionFieldMap_id_bijective c₀ c₁)
    t (ConcreteCategory.bijective_of_isIso _)

/-- Finite boundary representation, strict coefficient bound and the entire
acyclic module sequence are constructed from standard geometric order data.
The terminal unrounded divisor is identified with the transform along the
actual composite, not merely with a recursively prescribed boundary. -/
theorem snc_orderSeq_exists_rounded_boundary_model
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    [hX : IsIntegral X] [hNX : IsNoetherian X] [hsep : X.IsSeparated]
    [hOver : X.Over (Spec (.of k))] (n : ℕ)
    [hsmooth : SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    (S : BlowUpSequence X) (I : X.IdealSheafData) (m : ℕ)
    (hI : IsNonzeroEverywhere I) (hm : 1 ≤ m)
    (D : DivisorFamily X) (hD : D.IsSnc) (hS : S.IsOrderSeq (X ↘ Spec (.of k)) I D m)
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
      ∀ A : CartierDivisor X, blowUpSequenceAcyclicModules S
        (A + ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i).sheaf
        (cartierPullback S.composite A + ∑ i, ⌈-((b' i : ℝ) / (d : ℝ))⌉ • P' i).sheaf := by
  revert hX hNX hsep hOver hsmooth I m hI hm D hD hS P hP hPI b d hd c₀
  induction S with
  | nil X =>
    intro hX hNX hsep hOver hsmooth I m hI hm D hD hS P hP hPI b d hd c₀
    refine ⟨hX, hOver, hNX, hsmooth,
      (show IsDominant (𝟙 X) from inferInstance),
      (show Scheme.Hom.IsOver (𝟙 X) (Spec (.of k)) from inferInstance),
      dominantFunctionFieldMap_id_bijective, c₀, D, P, hP, b, hPI, hD, ?_, id, ?_⟩
    · change (∑ i, b i • P i) = cartierPullback (𝟙 X) (∑ i, b i • P i) - (d : ℤ) •
        birationalRelativeCanonicalDivisor n (𝟙 X) dominantFunctionFieldMap_id_bijective
          c₀ etaleCharts_cover c₀ etaleCharts_cover
      rw [cartierPullback_id, birationalRelativeCanonicalDivisor_id_eq_zero,
        smul_zero, sub_zero]
    · intro A
      change Nonempty (_ ≅ (cartierPullback (𝟙 X) A + _).sheaf)
      rw [cartierPullback_id]
      exact ⟨Iso.refl _⟩
  | cons X Z rest ih =>
    intro hX hNX hsep hOver hsmooth I m hI hm D hD hS P hP hPI b d hd c₀
    let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
    have hη := snc_orderSeq_genericPoint_notMem_first_center
      (X ↘ Spec (.of k)) n Z rest I D m hS hI hm
    obtain ⟨⟨hZsmooth, hZ, _⟩, hrest⟩ :=
      (isOrderSeq_cons_iff (X ↘ Spec (.of k)) I D m Z rest).mp hS
    let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
    let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
    let := Scheme.IdealSheafData.blowUp.isNoetherian Z
    let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
    let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
    let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
      snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
    let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
    let : Z.blowUp.IsSeparated := ⟨by
      rw [← Limits.terminal.comp_from Z.blowUpπ]
      infer_instance⟩
    let hπ := blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη
    obtain ⟨cT, _⟩ : ∃ cT : EtaleChart k Z.blowUp n, genericPoint Z.blowUp ∈ cT.U :=
      Opens.mem_iSup.mp ((etaleCharts_cover (K := k) (X := Z.blowUp) (n := n)).symm ▸
        Opens.mem_top (genericPoint Z.blowUp))
    obtain ⟨c, P₁, hP₁, hPI₁, hF₁, _, hstep⟩ :=
      snc_component_boundary_roundup_propagation (k := k) n D Z hD hZ hη P hP hPI
    let b₁ := sncComponentBoundaryCoefficients D Z c b d
    obtain ⟨hB₁, _, hb₁, hstep⟩ := hstep c₀ cT b d hd
    have hrest' := sncFamilyRefines_isOrderSeq
      (sncComponentTotalTransform_refines_totalTransform D Z
        (HasSncWith.isRegular (X ↘ Spec (.of k)) hZ)) hrest
    have hI' := isNonzeroEverywhere_weakTransform (X ↘ Spec (.of k)) Z hZsmooth I hI
    obtain ⟨hT, hTover, hTN, hTsmooth, hdom, hover, hσ, cY, F, P', hP', b',
      hPI', hF, hB', hb', hseq⟩ := ih (I.weakTransform Z) m hI' hm
        (sncComponentTotalTransform D Z) hF₁ hrest' P₁ hP₁ hPI₁ b₁ d hd cT
    let := hT
    let := hTover
    let := hTN
    let := hTsmooth
    let := hdom
    let := hover
    refine ⟨hT, hTover, hTN, hTsmooth,
      (show IsDominant (rest.composite ≫ Z.blowUpπ) from inferInstance),
      (show Scheme.Hom.IsOver (rest.composite ≫ Z.blowUpπ) (Spec (.of k)) from inferInstance),
      dominantFunctionFieldAlgHom_comp_bijective Z.blowUpπ rest.composite hπ hσ,
      cY, F, P', hP', b', hPI', hF, ?_, fun hb => hb' (hb₁ hb), ?_⟩
    · rw [hB', hB₁]
      exact relativeCanonical_boundary_transform_comp Z.blowUpπ rest.composite hπ hσ
        c₀ etaleCharts_cover cT etaleCharts_cover cY etaleCharts_cover _ d
    · intro A
      have htail := hseq (cartierPullback Z.blowUpπ A)
      rw [← cartierPullback_comp] at htail
      exact (hstep A).2.2.2 rest _ htail

end MixedFujita
