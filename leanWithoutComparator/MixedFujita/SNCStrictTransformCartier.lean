/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCSmoothDivisorCoefficients
public import MixedFujita.EffectiveCartierIdealProduct
public import MixedFujita.HironakaPrincipalizingRound
public import Hironaka.Scheme.BlowUp.Composite

/-! Cartier representatives of the actual SNC strict transforms.
The ideal-sheaf factorization constructs the component total-transform identities.
Uniform incidence on the original center is explicit; prime profiles and the relative
canonical divisor are separate geometric comparisons. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- The actual blow-up is integral and dominant, its exceptional divisor and
strict transforms have Cartier representatives, and the total transforms are
computed from incidence on the original center. -/
theorem snc_exists_strictTransform_cartier_totalTransform
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support) (contains : D.ι → Prop)
    (hcontains : ∀ i x, x ∈ Z.support →
      ((D.component i).stalkIdeal x ≤ Z.stalkIdeal x ↔ contains i))
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i) :
    let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
    let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
    let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
    ∃ (G : D.ι → CartierDivisor Z.blowUp) (E : CartierDivisor Z.blowUp),
      ∃ (hG : ∀ i, (G i).IsEffective) (hE : E.IsEffective),
        (∀ i, effectiveCartierIdealSheaf (G i) (hG i) = (D.component i).strictTransform Z) ∧
        effectiveCartierIdealSheaf E hE = Z.exceptionalDivisor ∧
        (∀ i, cartierPullback Z.blowUpπ (P i) = G i + if contains i then E else 0) ∧
        (∀ i (t : CodimensionOnePoint Z.blowUp), cartierCoefficient (G i) (t : Z.blowUp) =
          if (t : Z.blowUp) ∈ ((D.component i).strictTransform Z).support then 1 else 0) ∧
        (∀ t : CodimensionOnePoint Z.blowUp, cartierCoefficient E (t : Z.blowUp) =
          if (t : Z.blowUp) ∈ Z.exceptionalDivisor.support then 1 else 0) := by
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let := Scheme.IdealSheafData.blowUp.isProper_π Z
  let : Z.blowUp.IsSeparated := ⟨by
    rw [← terminal.comp_from Z.blowUpπ]
    infer_instance⟩
  obtain ⟨E, hE, hEI⟩ := exists_effectiveCartier_of_invertibleIdeal Z.exceptionalDivisor
    (Scheme.IdealSheafData.blowUp.isInvertible_comap_π Z)
  have hGex : ∀ i, ∃ (G : CartierDivisor Z.blowUp) (hG : G.IsEffective),
      effectiveCartierIdealSheaf G hG = (D.component i).strictTransform Z := fun i =>
    exists_effectiveCartier_of_invertibleIdeal _ (snc_strictTransform_isInvertible f D Z hD hZ i)
  choose G hG hGI using hGex
  refine ⟨G, E, hG, hE, hGI, hEI, ?_, ?_, ?_⟩
  · intro i
    have hI := snc_strictTransform_totalTransform f D Z hD hZ i (contains i) (hcontains i)
    by_cases hi : contains i
    · rw [ite_eq_left hi]
      apply cartierPullback_eq_add_of_ideal_product _ _ (hP i) _ _ (hG i) hE
      rw [hPI i, hGI i, hEI]
      simpa only [ite_eq_left hi] using hI
    · rw [ite_eq_right hi, add_zero]
      apply effectiveCartier_eq_of_idealSheaf_eq _ _
        (cartierPullback_isEffective Z.blowUpπ (P i) (hP i)) (hG i)
      rw [effectiveCartierIdealSheaf_cartierPullback Z.blowUpπ (P i) (hP i), hPI i, hGI i]
      simpa only [ite_eq_right hi, Scheme.IdealSheafData.mul_top] using hI
  · intro i t
    exact snc_totalTransform_cartierCoefficient f D Z hD hZ (toLex (Sum.inl i))
      (G i) (hG i) (hGI i) t
  · intro t
    exact snc_totalTransform_cartierCoefficient f D Z hD hZ (toLex (Sum.inr PUnit.unit))
      E hE hEI t

end MixedFujita
