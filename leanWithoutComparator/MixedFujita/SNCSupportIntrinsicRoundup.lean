/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentRelativeCanonical
public import MixedFujita.SNCComponentTotalTransform
public import MixedFujita.TwoSupportRoundup
public import MixedFujita.SNCCodimensionOneSupports

/-! Intrinsic rounding from SNC support profiles alone. Boundary members may
be empty or disconnected; they need no chosen generic points and may contain
whole components of the centre. Codimension-one disjointness of the actual
SNC total transform replaces the former boundary-avoidance hypotheses. -/

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

theorem snc_support_exists_intrinsic_roundup_with_dimensions
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
          C = cartierPullback Z.blowUpπ Q + ∑ i, j i • E i := by
  classical
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  let : Z.blowUp.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from Z.blowUpπ]
    infer_instance⟩
  dsimp only
  obtain ⟨c, E, hE, hc, hEI, hEc, hR⟩ :=
    snc_disconnectedCentre_exists_intrinsic_component_canonical_data (k := k) n D Z hD hZ hη
  choose G hG hGI using fun i => exists_effectiveCartier_of_invertibleIdeal _
    (snc_strictTransform_isInvertible (X ↘ Spec (.of k)) D Z hD hZ i)
  refine ⟨c, E, hE, hc, hEI, ?_⟩
  intro c₀ cT₀
  refine ⟨hR c₀ cT₀, ?_⟩
  intro m a b d hd
  let s : Z.componentFamily.ι → Finset (Fin m) := fun j =>
    Finset.univ.filter (fun i => D.component (a i) ≤ Z.componentFamily.component j)
  have hs : ∀ j, (s j).card ≤ (c j - 1) + 1 := by
    intro j
    let := (hc j).2.2
    let := sncCentre_component_isIntegral (X ↘ Spec (.of k)) D Z hZ j
    have hcount := snc_containing_components_card_le_codimension
      (X ↘ Spec (.of k)) n (c j) D (Z.componentFamily.component j)
      (sncCentre_component_hasSncWith (X ↘ Spec (.of k)) D Z hZ j) (hc j).2.1
      ((s j).map a) (by
        intro i hi
        obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hi
        exact (Finset.mem_filter.mp hl).2)
    rw [Finset.card_map] at hcount
    have := (hc j).1
    omega
  have hPG : ∀ i, cartierPullback Z.blowUpπ (P (a i)) =
      G (a i) + ∑ j, if i ∈ s j then E j else 0 := by
    intro i
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using
      snc_disconnectedCentre_cartier_totalTransform (X ↘ Spec (.of k)) D Z hD hZ
        (a i) (P (a i)) (hP (a i)) (hPI (a i)) (G (a i)) (hG (a i)) (hGI (a i)) E hE hEI
  refine ⟨?_, ?_⟩
  · exact snc_cartier_roundup_sum_coefficient (X ↘ Spec (.of k)) D hD P hP hPI a b d
  · apply cartier_construct_roundup_two_support_totalTransform Z.blowUpπ (fun i => P (a i))
      (fun i => ((D.component (a i)).strictTransform Z).support) ?_
      (fun i => G (a i))
      (fun i => snc_totalTransform_cartierCoefficient (X ↘ Spec (.of k)) D Z hD hZ
        (toLex (Sum.inl (a i))) (G (a i)) (hG (a i)) (hGI (a i)))
      (fun j => {t | Z.blowUpπ t ∈ (Z.componentFamily.component j).support})
      (fun _ _ _ hi hj => Hironaka.Sequence.eq_of_mem_support_componentFamily Z
        (HasSncWith.isRegular (X ↘ Spec (.of k)) hZ) hi hj) E hEc ?_
      s (fun j => c j - 1) hs hPG _ (hR c₀ cT₀) b d hd
    · intro t i j hi hj
      have h := snc_component_eq_of_mem_support_codimensionOne (D.totalTransform Z)
        (totalTransform_isSnc (X ↘ Spec (.of k)) D Z hD hZ) t
        (toLex (Sum.inl (a i))) (toLex (Sum.inl (a j))) hi hj
      have h' : (Sum.inl (a i) : D.ι ⊕ PUnit.{u + 1}) = Sum.inl (a j) := h
      exact a.injective (Sum.inl.inj h')
    · intro t i j hi hj
      apply snc_strictTransform_support_disjoint_exceptional_codimensionOne
        (X ↘ Spec (.of k)) D Z hD hZ t (a i) hi
      exact (mem_support_comap_iff_apply Z Z.blowUpπ _).mpr
        (centre_component_support_subset Z j hj)

end MixedFujita
