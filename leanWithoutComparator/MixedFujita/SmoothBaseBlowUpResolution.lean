/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence
public import Hironaka.Scheme.ProjectiveBundle.BlowUp

/-!+A smooth modification of the base chosen as a single blow-up. Hironaka's Main Theorem I
supplies its centre on the singular locus. This retains the ideal needed to lift a source
model by principalization, rather than merely supplying an unrelated smooth base model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {k : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- A smooth projective birational modification of the base can be chosen as one blow-up,
with centre supported precisely on its singular locus. Projective embeddings over the field
lift to this same model. -/
theorem exists_smooth_base_single_blowUp (cY : EtaleChart K Y k) :
    ∃ I : Y.IdealSheafData, (I.support : Set Y) = Y.singularLocus ∧
      genericPoint Y ∉ (I.support : Set Y) ∧
      ∃ (_ : IsIntegral I.blowUp) (_ : I.blowUp.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian I.blowUp)
        (_ : SmoothOfRelativeDimension k (I.blowUp ↘ Spec (CommRingCat.of K)))
        (_ : IsDominant I.blowUpπ) (_ : I.blowUpπ.IsOver (Spec (CommRingCat.of K)))
        (_ : IsProper I.blowUpπ) (_ : IsProjective I.blowUpπ),
        Function.Bijective (dominantFunctionFieldAlgHom (K := K) I.blowUpπ) ∧
        ∀ (N : ℕ) (e : Y ⟶ polynomialProjectiveScheme N K), IsClosedImmersion e →
          e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K) →
          ∃ (M : ℕ) (e' : I.blowUp ⟶ polynomialProjectiveScheme M K),
            IsClosedImmersion e' ∧
            e' ≫ polynomialProjectiveToBase M K = I.blowUp ↘ Spec (CommRingCat.of K) := by
  classical
  have hYN : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  have hYc : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of K))
  have hYnoeth : IsNoetherian Y :=
    { toIsLocallyNoetherian := hYN, toCompactSpace := hYc }
  let Yk : AlgScheme K :=
    MorphismProperty.Over.mk ⊤ (Y ↘ Spec (CommRingCat.of K)) ⟨inferInstance, inferInstance⟩
  have hYi : IsIntegral Yk.left := ‹IsIntegral Y›
  obtain ⟨I, hsupp, hreg⟩ : ∃ I : Y.IdealSheafData,
      (I.support : Set Y) = Y.singularLocus ∧ IsRegular I.blowUp :=
    exists_support_eq_singularLocus_isRegular_blowUp Yk
  have hη : genericPoint Y ∉ (I.support : Set Y) := by
    rw [hsupp]
    exact fun h => h Hironaka.Resolution.isRegularAt_genericPoint_of_isIntegral
  have hBi : IsIntegral I.blowUp := blowUp_isIntegral_of_genericPoint_notMem_support I hη
  have hπdom : IsDominant I.blowUpπ := blowUp_isDominant_of_genericPoint_notMem_support I hη
  have hπprop : IsProper I.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π I
  have hπproj : IsProjective I.blowUpπ := I.isProjective_blowUpπ
  let instB : I.blowUp.Over (Spec (CommRingCat.of K)) :=
    ⟨I.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  have hπover : I.blowUpπ.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hBN : IsLocallyNoetherian I.blowUp :=
    LocallyOfFiniteType.isLocallyNoetherian I.blowUpπ
  have hBc : CompactSpace I.blowUp :=
    QuasiCompact.compactSpace_of_compactSpace I.blowUpπ
  have hBnoeth : IsNoetherian I.blowUp :=
    { toIsLocallyNoetherian := hBN, toCompactSpace := hBc }
  have hsm : SmoothOfRelativeDimension k (I.blowUp ↘ Spec (CommRingCat.of K)) := by
    change SmoothOfRelativeDimension k (I.blowUpπ ≫ (Y ↘ Spec (CommRingCat.of K)))
    simpa only [blowUpSequence_single_composite] using
      blowUpSequence_smoothOfRelativeDimension_of_centers_over
        (Scheme.BlowUpSequence.cons Y I (Scheme.BlowUpSequence.nil I.blowUp)) I.support
        (blowUpSequence_single_centers_over I) hη hreg cY
  have hbir : Function.Bijective (dominantFunctionFieldAlgHom (K := K) I.blowUpπ) :=
    dominantFunctionFieldMap_bijective_of_isIso_stalkMap I.blowUpπ
      (blowUp_isIso_stalkMap_of_notMem_support I (genericPoint I.blowUp)
        (by rw [dominant_map_genericPoint]; exact hη))
  refine ⟨I, hsupp, hη, hBi, instB, hBnoeth, hsm, hπdom, hπover, hπprop, hπproj,
    hbir, ?_⟩
  intro N e he hover
  letI : IsClosedImmersion e := he
  obtain ⟨M, e', he', hover'⟩ := exists_closedImmersion_blowUp_of_projective e hover I
  exact ⟨M, e', he', hover'⟩

end MixedFujita
