/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineBlowupReesSections
public import MixedFujita.RegularCartierSGATransitions

/-! The actual exceptional ideal has the explicit Rees constant generators.
Their transition formula constructs its Cartier divisor and Rees twisting sheaf. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (I : Ideal R)

theorem reesConstantSection_generates_exceptional (a : I)
    (W : (affineBlowUp I).Opens) (hW : IsAffineOpen W)
    (hWeq : W = Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) :
    reesConstantSection I (a : R) W ∈ nonZeroDivisors Γ(affineBlowUp I, W) ∧
      (affineBlowUp.exceptionalIdeal I).ideal ⟨W, hW⟩ =
        Ideal.span {reesConstantSection I (a : R) W} := by
  have hWimage : W = affineBlowUp.chart I a ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, affineBlowUp.opensRange_chart, hWeq]
  subst hWimage
  let j := affineBlowUp.chart I a
  let e := (j.appIso ⊤).commRingCatIsoToRingEquiv
  let ψ : Γ(Spec (.of (affineBlowUpAlgebra I a)), ⊤) →+*
      Γ(affineBlowUp I, j ''ᵁ ⊤) := e.symm
  have hψs : Function.Surjective ψ := e.symm.surjective
  have he : e (reesConstantSection I (a : R) (j ''ᵁ ⊤)) =
      affineBlowUp.chartGenerator I a := by
    change (j.appIso ⊤).hom _ = _
    rw [Scheme.Hom.appIso_hom']
    dsimp only [j]
    have H (V : (affineBlowUp I).Opens)
        (hV : V = Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a))
        (h : (⊤ : (Spec (.of (affineBlowUpAlgebra I a))).Opens) ≤
          affineBlowUp.chart I a ⁻¹ᵁ V) :
        (affineBlowUp.chart I a).appLE V ⊤ h (reesConstantSection I (a : R) V) =
          affineBlowUp.chartGenerator I a := by
      subst hV
      exact affineBlowUp_chart_appLE_constant I a (a : R) h
    exact H _ hWeq _
  have hgen : ψ (affineBlowUp.chartGenerator I a) =
      reesConstantSection I (a : R) (j ''ᵁ ⊤) := by
    change e.symm (affineBlowUp.chartGenerator I a) = _
    rw [← he, e.symm_apply_apply]
  constructor
  · rw [← hgen]
    exact map_mem_nonZeroDivisors_of_ringEquiv e.symm
      (affineBlowUp.chartGenerator_mem_nonZeroDivisors I a)
  · have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
      (affineBlowUp.exceptionalIdeal I) j ⟨⊤, isAffineOpen_top _⟩
    rw [affineBlowUp.ideal_comap_exceptionalIdeal_chart_top] at h1
    have hψ : (j.appIso ⊤).inv.hom = ψ := RingHom.ext fun _ => rfl
    rw [hψ] at h1
    have h2 := congrArg (Ideal.map ψ) h1
    rw [Ideal.map_comap_of_surjective ψ hψs, Ideal.map_span,
      Set.image_singleton, hgen] at h2
    exact h2.symm

theorem reesChart_nonempty [IsDomain R] (a : I) (ha : (a : R) ≠ 0) :
    Nonempty (Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)) := by
  refine ⟨⟨affineBlowUpZeroPoint I a ha, ?_⟩⟩
  change reesAlgebra.degreeOne I a ∉ (⊥ : Ideal (reesAlgebra I))
  intro h
  have hc := congrArg (fun p : reesAlgebra I => Polynomial.coeff (p : Polynomial R) 1)
    (Ideal.mem_bot.mp h)
  apply ha
  simpa [reesAlgebra.coe_degreeOne] using hc

variable [IsDomain R] {ι : Type u} (a : ι → I) (ha : ∀ i, (a i : R) ≠ 0)
  (hcov : ⨆ i, Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I (a i)) = ⊤)

include ha hcov in
theorem exists_exceptionalCartier_reesTwisting [Nonempty ι] :
    let := affineBlowUp_isIntegral_of_ne_bot I (by
      intro hI
      let i : ι := Classical.choice inferInstance
      exact ha i (Ideal.mem_bot.mp (hI ▸ (a i).2)))
    ∃ (E : CartierDivisor (affineBlowUp I)) (hE : E.IsEffective),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal I ∧
      Nonempty ((-E).sheaf ≅
        (Proj.twistingSheaf (reesAlgebra.grading I) (fun i => reesAlgebra.degreeOne I (a i))
          (fun i => reesAlgebra.degreeOne_mem (a i)) hcov).toModules 1) := by
  let := affineBlowUp_isIntegral_of_ne_bot I (by
    intro hI
    let i : ι := Classical.choice inferInstance
    exact ha i (Ideal.mem_bot.mp (hI ▸ (a i).2)))
  let L := Proj.twistingSheaf (reesAlgebra.grading I) (fun i => reesAlgebra.degreeOne I (a i))
    (fun i => reesAlgebra.degreeOne_mem (a i)) hcov
  have : ∀ i, Nonempty (L.U i) := fun i => reesChart_nonempty I (a i) (ha i)
  let hAff : ∀ i, IsAffineOpen (L.U i) := fun i =>
    Proj.isAffineOpen_basicOpen _ _ (reesAlgebra.degreeOne_mem (a i)) one_pos
  apply exists_effectiveCartier_sga_of_generators L (affineBlowUp.exceptionalIdeal I) hAff
    (fun i => reesConstantSection I (a i : R) (L.U i))
  · intro i
    exact nonZeroDivisors.ne_zero (reesConstantSection_generates_exceptional I (a i) _ (hAff i) rfl).1
  · intro i
    exact (reesConstantSection_generates_exceptional I (a i) _ (hAff i) rfl).2
  · intro i j
    exact reesConstantSection_transition I (a i) (a j)

end MixedFujita
