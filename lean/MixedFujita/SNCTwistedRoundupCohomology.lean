/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCSupportSequenceMatching
public import MixedFujita.ActualAcyclicCohomologyDescent

/-!
Geometric all-degree comparison for arbitrary Cartier twists of an SNC roundup.

The same actual centre components supply the codimensions, exceptional divisors,
roundup corrections and relative vanishing. No acyclicity or direct-image
isomorphism is assumed. Centres and boundary members may be disconnected, and a
centre component may lie in a boundary member.

The result also prepends this geometric step to the existing analytic sequence
interface. Propagating unrounded boundary data through an entire resolution and
handling a singular klt target remain separate obligations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme MonoidalCategory
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

/-- A bounded effective exceptional correction admits the actual direct-image
comparison for an arbitrary Cartier divisor, without an effective decomposition. -/
theorem bounded_cartier_correction_pushforward_iso
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    {J : Type*} [Fintype J] (E : J → CartierDivisor T)
    (hE : ∀ i, (E i).IsEffective) (r j : J → ℕ) (hj : ∀ i, j i ≤ r i)
    (hr : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient (∑ i, r i • E i) (t : T) = 0)
    (Q : CartierDivisor X) (C : CartierDivisor T)
    (hC : C = cartierPullback ρ Q + ∑ i, j i • E i) :
    Nonempty (Q.sheaf ≅ (Scheme.Modules.pushforward ρ).obj C.sheaf) := by
  let F := ∑ i, j i • E i
  have hF : F.IsEffective := component_exceptional_correction_isEffective E hE j
  have hEx : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient F (t : T) = 0 := by
    intro t ht
    exact bounded_effective_correction_coefficient_zero E hE r j hj _ (hr t ht)
  obtain ⟨e⟩ := cartierPullback_sheaf_iso_modulePullback_of_dominant ρ Q
  exact ⟨effectiveExceptionalCartierTwistedPushforwardIso hnormX hnormT ρ hρ F hF hEx Q ≪≫
    (Scheme.Modules.pushforward ρ).mapIso
      (tensorIso e (Iso.refl _) ≪≫ cartierTensorSheafIso _ F ≪≫
        eqToIso (congrArg CartierDivisor.sheaf hC.symm))⟩

/-- Every arbitrary Cartier twist of a geometrically matched SNC roundup has
relative acyclicity, actual all-degree cohomology comparison and sequence
prepending. Only geometric SNC and coefficient data are inputs to this step. -/
theorem snc_support_roundup_twisted_cohomology_comparison
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
    ∀ (c₀ : EtaleChart k X n) (cT₀ : EtaleChart k Z.blowUp n)
      (m : ℕ) (a : Fin m ↪ D.ι) (b : Fin m → ℤ) (d : ℕ), 1 ≤ d →
    ∀ (Q : CartierDivisor X) (C : CartierDivisor Z.blowUp),
      (∀ t : CodimensionOnePoint X, cartierCoefficient Q (t : X) =
        ⌈-((cartierCoefficient (∑ i, b i • P (a i)) (t : X) : ℝ) / (d : ℝ))⌉) →
      (∀ t : CodimensionOnePoint Z.blowUp, cartierCoefficient C (t : Z.blowUp) =
        ⌈-((cartierCoefficient
          (cartierPullback Z.blowUpπ (∑ i, b i • P (a i)) - (d : ℤ) •
            birationalRelativeCanonicalDivisor n Z.blowUpπ hπ
              c₀ etaleCharts_cover cT₀ etaleCharts_cover) (t : Z.blowUp) : ℝ) / (d : ℝ))⌉) →
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
  let hπ := blowUp_functionField_bijective_of_genericPoint_notMem_support Z hη
  dsimp only
  intro c₀ cT₀ m a b d hd Q C hQ hC A
  obtain ⟨c, E, hE, hc, hEI, hdata⟩ :=
    snc_support_exists_intrinsic_roundup_with_dimensions (k := k) n D Z hD hZ hη P hP hPI
  obtain ⟨hR, hb⟩ := hdata c₀ cT₀
  obtain ⟨hQ', C', j, hj, hC', hdecomp⟩ := hb m a b d hd
  have hQQ : Q = ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P (a i) :=
    cartier_roundup_unique hnormX _ _ _ d hQ hQ'
  have hCC : C = C' := cartier_roundup_unique hnormT _ _ _ d hC hC'
  rw [← hQQ, ← hCC] at hdecomp
  have hbound : ∀ t : CodimensionOnePoint Z.blowUp,
      Order.coheight (Z.blowUpπ (t : Z.blowUp)) = 1 →
      cartierCoefficient (∑ i, (c i - 1) • E i) (t : Z.blowUp) = 0 := by
    intro t ht
    rw [← hR]
    exact relativeCanonical_coefficient_zero_over_normal_prime Z.blowUpπ hπ hnormX hnormT
      c₀ etaleCharts_cover cT₀ etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective Z.blowUpπ hπ c₀ cT₀) t ht
  have htwist : cartierPullback Z.blowUpπ A + C =
      cartierPullback Z.blowUpπ (A + Q) + ∑ i, j i • E i := by
    rw [hdecomp, cartierPullback_add]
    abel
  obtain ⟨hv, _⟩ := sncCentre_cartier_correction_relative_vanishing
    (X ↘ Spec (.of k)) n D Z hZ hη c hc E hE hEI
    (A + Q) (cartierPullback Z.blowUpπ A + C) j hj htwist
  obtain ⟨e⟩ := bounded_cartier_correction_pushforward_iso hnormX hnormT Z.blowUpπ hπ
    E hE (fun i => c i - 1) j hj hbound (A + Q) _ htwist
  let := (A + Q).isInvertible_sheaf
  let := invertibleModule_isQuasicoherent (A + Q).sheaf
  refine ⟨⟨e⟩, hv, fun q => ⟨acyclicPushforwardActualCohomologyAddEquiv
    Z.blowUpπ _ (A + Q).sheaf e hv q⟩, ?_⟩
  intro rest N hrest
  let := (cartierPullback Z.blowUpπ A + C).isInvertible_sheaf
  let := invertibleModule_isQuasicoherent (cartierPullback Z.blowUpπ A + C).sheaf
  exact ⟨_, inferInstance, ⟨e⟩, hv, hrest⟩

end MixedFujita
