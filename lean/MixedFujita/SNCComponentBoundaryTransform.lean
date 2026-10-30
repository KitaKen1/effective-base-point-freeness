/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentTransformFamily
public import MixedFujita.SNCComponentRelativeCanonical
public import MixedFujita.SNCSupportIntrinsicRoundup

/-! Finite SNC boundary data survive an actual blow-up, including disconnected
centres with different component codimensions. The exceptional coefficient is
the sum of incident boundary coefficients minus d times codimension minus one.
This is an equality of Cartier divisors before rounding, not just an equality
of supports or a prescribed transformation hypothesis. -/

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

/-- The integral numerator of the crepant boundary on the split transform. -/
noncomputable def sncComponentBoundaryCoefficients
    {X : Scheme.{u}} [NoetherianSpace X] (D : DivisorFamily X) (Z : X.IdealSheafData)
    (c : Z.componentFamily.ι → ℕ) (b : D.ι → ℤ) (d : ℕ) :
    (sncComponentTotalTransform D Z).ι → ℤ :=
  fun i => Sum.elim b (fun j =>
    (∑ i ∈ Finset.univ.filter (fun i => D.component i ≤ Z.componentFamily.component j), b i) -
      (d : ℤ) * ((c j - 1 : ℕ) : ℤ)) (ofLex i)

/-- Reindex the existing finite SNC rounding theorem by the whole boundary
family. Zero coefficients accommodate unselected boundary members. -/
theorem snc_cartier_roundup_family_coefficient
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (D : DivisorFamily X) (hD : D.IsSnc)
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i)
    (b : D.ι → ℤ) (d : ℕ) (t : CodimensionOnePoint X) :
    cartierCoefficient (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P i) (t : X) =
      ⌈-((cartierCoefficient (∑ i, b i • P i) (t : X) : ℝ) / (d : ℝ))⌉ := by
  classical
  let e := (Fintype.equivFin D.ι).symm
  have hs (a : D.ι → ℤ) : (∑ i, a (e i) • P (e i)) = ∑ i, a i • P i :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  have h := snc_cartier_roundup_sum_coefficient f D hD P hP hPI
    e.toEmbedding (b ∘ e) d t
  simp only [Function.comp_apply, Equiv.toEmbedding_apply] at h
  rw [hs (fun i => ⌈-((b i : ℝ) / (d : ℝ))⌉), hs b] at h
  exact h

/-- Construct all transformed Cartier members and their exact crepant boundary
formula from the original SNC geometry. The split family stays SNC and is
compatible with any next centre compatible with the ordinary total transform. -/
theorem snc_component_crepant_boundary_transform
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
      (∀ j, 0 < c j ∧ c j ≤ n ∧ SmoothOfRelativeDimension (n - c j)
        ((Z.componentFamily.component j).subschemeι ≫ (X ↘ Spec (.of k)))) ∧
      (∀ i, effectiveCartierIdealSheaf (P' i) (hP' i) = F.component i) ∧
      F.IsSnc ∧
      (∀ W, (D.totalTransform Z).HasSncWith W → F.HasSncWith W) ∧
      ∀ (c₀ : EtaleChart k X n) (cT₀ : EtaleChart k Z.blowUp n) (b : D.ι → ℤ) (d : ℕ),
        ∑ i, sncComponentBoundaryCoefficients D Z c b d i • P' i =
          cartierPullback Z.blowUpπ (∑ i, b i • P i) - (d : ℤ) •
            birationalRelativeCanonicalDivisor n Z.blowUpπ hπ
              c₀ etaleCharts_cover cT₀ etaleCharts_cover := by
  classical
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  let : Z.blowUp.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from Z.blowUpπ]
    infer_instance⟩
  dsimp only
  obtain ⟨c, E, hE, hc, hEI, _, hR⟩ :=
    snc_disconnectedCentre_exists_intrinsic_component_canonical_data (k := k) n D Z hD hZ hη
  choose G hG hGI using fun i => exists_effectiveCartier_of_invertibleIdeal _
    (snc_strictTransform_isInvertible (X ↘ Spec (.of k)) D Z hD hZ i)
  let F := sncComponentTotalTransform D Z
  let P' : F.ι → CartierDivisor Z.blowUp := fun i => Sum.elim G E (ofLex i)
  have hP' : ∀ i, (P' i).IsEffective := by
    intro i
    rcases i with i | j
    · exact hG i
    · exact hE j
  refine ⟨c, P', hP', hc, ?_, sncComponentTotalTransform_isSnc
    (X ↘ Spec (.of k)) D Z hD hZ,
    fun W => sncComponentTotalTransform_hasSncWith D Z
      (HasSncWith.isRegular (X ↘ Spec (.of k)) hZ) W, ?_⟩
  · intro i
    rcases i with i | j
    · exact hGI i
    · exact hEI j
  · intro c₀ cT₀ b d
    have hPG : ∀ i, cartierPullback Z.blowUpπ (P i) =
        G i + ∑ j, if D.component i ≤ Z.componentFamily.component j then E j else 0 :=
      fun i => snc_disconnectedCentre_cartier_totalTransform (X ↘ Spec (.of k)) D Z hD hZ
        i (P i) (hP i) (hPI i) (G i) (hG i) (hGI i) E hE hEI
    let pb : CartierDivisor X →+ CartierDivisor Z.blowUp :=
      { toFun := cartierPullback Z.blowUpπ
        map_zero' := cartierPullback_zero _
        map_add' := cartierPullback_add _ }
    have hpb : cartierPullback Z.blowUpπ (∑ i, b i • P i) =
        ∑ i, b i • cartierPullback Z.blowUpπ (P i) :=
      (map_sum pb _ _).trans (Finset.sum_congr rfl (fun i _ => map_zsmul pb (b i) (P i)))
    have hs : (∑ i : F.ι, sncComponentBoundaryCoefficients D Z c b d i • P' i) =
        (∑ i, b i • G i) + ∑ j,
          ((∑ i ∈ Finset.univ.filter
            (fun i => D.component i ≤ Z.componentFamily.component j), b i) -
            (d : ℤ) * ((c j - 1 : ℕ) : ℤ)) • E j := by
      have he := Fintype.sum_equiv (toLex : (D.ι ⊕ Z.componentFamily.ι) ≃ F.ι)
        (fun i => sncComponentBoundaryCoefficients D Z c b d (toLex i) • P' (toLex i))
        (fun i => sncComponentBoundaryCoefficients D Z c b d i • P' i) (fun _ => rfl)
      rw [Fintype.sum_sum_type] at he
      exact he.symm
    rw [hs, hpb, hR c₀ cT₀]
    simp_rw [hPG, smul_add, Finset.smul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have hsum : (∑ j, ∑ i, b i •
        (if D.component i ≤ Z.componentFamily.component j then E j else 0)) =
        ∑ j, (∑ i ∈ Finset.univ.filter
          (fun i => D.component i ≤ Z.componentFamily.component j), b i) • E j := by
      apply Finset.sum_congr rfl
      intro j _
      simp [smul_ite, Finset.sum_filter, Finset.sum_smul]
    rw [hsum]
    simp_rw [sub_smul, ← natCast_zsmul (E _) (c _ - 1), smul_smul]
    rw [Finset.sum_sub_distrib]
    abel

/-- The strict SNC coefficient bound b_i/d < 1 survives the crepant transform.
Only the upper bound is asserted: exceptional coefficients may be negative. -/
theorem snc_component_boundary_coefficients_lt_denominator
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (c : Z.componentFamily.ι → ℕ)
    (hc : ∀ j, 0 < c j ∧ c j ≤ n ∧ SmoothOfRelativeDimension (n - c j)
      ((Z.componentFamily.component j).subschemeι ≫ f))
    (b : D.ι → ℤ) (d : ℕ) (hd : 1 ≤ d) (hb : ∀ i, b i < (d : ℤ)) :
    ∀ i, sncComponentBoundaryCoefficients D Z c b d i < (d : ℤ) := by
  classical
  let : Smooth f := SmoothOfRelativeDimension.smooth n _
  intro i
  rcases i with i | j
  · exact hb i
  · let s := Finset.univ.filter (fun i => D.component i ≤ Z.componentFamily.component j)
    let := (hc j).2.2
    let := sncCentre_component_isIntegral f D Z hZ j
    have hcard := snc_containing_components_card_le_codimension f n (c j) D
      (Z.componentFamily.component j) (sncCentre_component_hasSncWith f D Z hZ j)
      (hc j).2.1 s (fun i hi => (Finset.mem_filter.mp hi).2)
    have hsum : (∑ i ∈ s, b i) ≤ (s.card : ℤ) * ((d : ℤ) - 1) := by
      calc
        (∑ i ∈ s, b i) ≤ ∑ _i ∈ s, ((d : ℤ) - 1) :=
          Finset.sum_le_sum (fun i _ => by have := hb i; omega)
        _ = _ := by simp [mul_sub]
    have hcardZ : (s.card : ℤ) ≤ (c j : ℤ) := by exact_mod_cast hcard
    have hdZ : (0 : ℤ) ≤ (d : ℤ) - 1 := by omega
    have hprod := mul_le_mul_of_nonneg_right hcardZ hdZ
    have hcZ : (0 : ℤ) < (c j : ℤ) := by exact_mod_cast (hc j).1
    have hsub : ((c j - 1 : ℕ) : ℤ) = (c j : ℤ) - 1 := by omega
    change (∑ i ∈ s, b i) - (d : ℤ) * ((c j - 1 : ℕ) : ℤ) < (d : ℤ)
    rw [hsub]
    nlinarith

end MixedFujita
