/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCSmoothDivisorCoefficients
public import MixedFujita.DisjointSupportRoundup
public import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
public import Hironaka.Scheme.Snc.Family

/-! At a codimension-one point an SNC family has at most one active member.
This permits coefficientwise rounding without irreducible components or
chosen generic points, including empty and disconnected family members. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Classical.propDecidable

theorem snc_component_eq_of_mem_support_codimensionOne
    {X : Scheme.{u}} (D : DivisorFamily X) (hD : D.IsSnc)
    (t : CodimensionOnePoint X) (i j : D.ι)
    (hi : (t : X) ∈ (D.component i).support)
    (hj : (t : X) ∈ (D.component j).support) : i = j := by
  obtain ⟨n, z, hz, c, hc, _⟩ := hD.2 (t : X)
  have hn : n = 1 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, t.property] at h
    exact_mod_cast h
  subst n
  exact congrArg Subtype.val (hc (Subsingleton.elim (c ⟨i, hi⟩) (c ⟨j, hj⟩)))

theorem snc_cartier_support_profile
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (D : DivisorFamily X) (hD : D.IsSnc)
    (i : D.ι) (P : CartierDivisor X) (hP : P.IsEffective)
    (hPI : effectiveCartierIdealSheaf P hP = D.component i)
    (t : CodimensionOnePoint X) :
    cartierCoefficient P (t : X) = if (t : X) ∈ (D.component i).support then 1 else 0 := by
  let := isRegularLocalRing_stalk f (t : X)
  let : IsDiscreteValuationRing (X.presheaf.stalk (t : X)) := inferInstance
  exact smoothDivisor_cartierCoefficient _
    (isSmoothDivisor_of_snc_data D.component hD.1 (isSnc_data D hD)
      (fun x => isRegularLocalRing_stalk f x) i) P hP hPI t

theorem snc_cartier_roundup_sum_coefficient
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (D : DivisorFamily X) (hD : D.IsSnc)
    (P : D.ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (hPI : ∀ i, effectiveCartierIdealSheaf (P i) (hP i) = D.component i)
    {m : ℕ} (a : Fin m ↪ D.ι) (b : Fin m → ℤ) (d : ℕ) (t : CodimensionOnePoint X) :
    cartierCoefficient (∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P (a i)) (t : X) =
      ⌈-((cartierCoefficient (∑ i, b i • P (a i)) (t : X) : ℝ) / (d : ℝ))⌉ := by
  apply cartier_roundup_support_sum_coefficient (fun i => (D.component (a i)).support)
  · intro t i j hi hj
    exact a.injective (snc_component_eq_of_mem_support_codimensionOne D hD t _ _ hi hj)
  · exact fun i => snc_cartier_support_profile f D hD (a i) (P (a i)) (hP (a i)) (hPI (a i))

theorem snc_strictTransform_support_disjoint_exceptional_codimensionOne
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    (t : CodimensionOnePoint Z.blowUp) (i : D.ι)
    (hi : (t : Z.blowUp) ∈ ((D.component i).strictTransform Z).support) :
    (t : Z.blowUp) ∉ Z.exceptionalDivisor.support := by
  intro he
  have h := snc_component_eq_of_mem_support_codimensionOne (D.totalTransform Z)
    (totalTransform_isSnc f D Z hD hZ) t (toLex (Sum.inl i))
    (toLex (Sum.inr PUnit.unit)) hi he
  have h' : (Sum.inl i : D.ι ⊕ PUnit.{u + 1}) = Sum.inr PUnit.unit := h
  cases h'

end MixedFujita
