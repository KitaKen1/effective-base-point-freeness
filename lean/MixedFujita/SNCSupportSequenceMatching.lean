/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierRoundupCompatibility
public import MixedFujita.BlowUpSequenceAcyclicPushforward
public import MixedFujita.SNCSupportRoundupPushforward

/-! A separately constructed Cartier roundup is identified with the intrinsic
one by its codimension-one coefficients. This supplies the analytic data for
one SNC step and prepends that step to an actual Hironaka blow-up sequence.
Boundary generic points and boundary avoidance of the centre are not required.
The tail's step data are explicit; propagating finite SNC boundary representations
along an arbitrary sequence is a separate remaining task. -/

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

theorem snc_support_matched_roundup_acyclic_cons
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
      Nonempty (Q.sheaf ≅ (Scheme.Modules.pushforward Z.blowUpπ).obj C.sheaf) ∧
      (∀ U : X.Opens, IsAffineOpen U → ∀ q : ℕ,
        Subsingleton (C.sheaf.H' (q + 1) (Z.blowUpπ ⁻¹ᵁ U))) ∧
      (∀ q : ℕ, Limits.IsZero (cohomologicalDirectImage Z.blowUpπ C.sheaf (q + 1))) ∧
      (∀ (rest : BlowUpSequence Z.blowUp) (N : rest.last.Modules),
        blowUpSequenceAcyclicModules rest C.sheaf N →
        blowUpSequenceAcyclicModules (.cons X Z rest) Q.sheaf N) := by
  let := blowUp_isIntegral_of_genericPoint_notMem_support Z hη
  let := blowUp_isDominant_of_genericPoint_notMem_support Z hη
  let := Scheme.IdealSheafData.blowUp.isLocallyNoetherian Z
  let : Z.blowUp.Over (Spec (.of k)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of k))⟩
  let : Z.blowUpπ.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of k)) :=
    snc_disconnectedCentre_blowUp_smoothOfRelativeDimension (X ↘ Spec (.of k)) n D Z hZ hη
  let : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (Z.blowUp ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth n _
  have hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := k) x
  have hnormT : ∀ t : Z.blowUp, IsIntegrallyClosed (Z.blowUp.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := k) t
  dsimp only
  intro c₀ cT₀ m a b d hd Q C hQ hC
  obtain ⟨_, _, _, _, _, hdata⟩ :=
    snc_support_exists_intrinsic_roundup_pushforward_comparison (k := k)
      n D Z hD hZ hη P hP hPI
  obtain ⟨hQ', C', _, _, hC', _, hv, hz, he, _, _⟩ := (hdata c₀ cT₀).2 m a b d hd
  have hQQ : Q = ∑ i, ⌈-((b i : ℝ) / (d : ℝ))⌉ • P (a i) :=
    cartier_roundup_unique hnormX _ _ _ d hQ hQ'
  have hCC : C = C' := cartier_roundup_unique hnormT _ _ _ d hC hC'
  rw [← hQQ, ← hCC] at he
  rw [← hCC] at hv hz
  refine ⟨he, hv, hz, ?_⟩
  intro rest N hrest
  let := C.isInvertible_sheaf
  let := invertibleModule_isQuasicoherent C.sheaf
  exact ⟨C.sheaf, inferInstance, he, hv, hrest⟩

end MixedFujita
