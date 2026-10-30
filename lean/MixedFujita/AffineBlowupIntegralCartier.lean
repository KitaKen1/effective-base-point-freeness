/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalCartierRestrictionLayers
public import MixedFujita.ActualBlowupInfinitesimalSheaves
public import Hironaka.Scheme.BlowUp.Transform.Reduced
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Basic

/-! A nonzero ideal in a domain has an integral actual affine blow-up.
Its actual exceptional ideal constructs an effective Cartier divisor, so the
restriction description of every infinitesimal layer needs no supplied divisor. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial
open TauCeti.AlgebraicGeometry.Scheme
open CohomologyAux
open scoped HomogeneousIdeal
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (I : Ideal R)

theorem affineBlowUp_isReduced_of_base_reduced [_root_.IsReduced R] :
    IsReduced (affineBlowUp I) := by
  let U := (affineBlowUp.affineOpenCover I).openCover
  have : ∀ i, IsReduced (U.X i) := by
    intro i
    change IsReduced (Spec (.of (affineBlowUpAlgebra I ((i : I).1))))
    infer_instance
  exact IsReduced.of_openCover _ U

variable [IsDomain R]

noncomputable def affineBlowUpZeroPoint (a : I) (ha : (a : R) ≠ 0) : affineBlowUp I where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using
      (inferInstance : (⊥ : Ideal (reesAlgebra I)).IsPrime)
  not_irrelevant_le := by
    intro h
    have hz : reesAlgebra.degreeOne I a = 0 := Ideal.mem_bot.mp
      (h (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one (reesAlgebra.degreeOne_mem a)))
    have hc := congrArg (fun p : reesAlgebra I => Polynomial.coeff (p : R[X]) 1) hz
    apply ha
    simpa [reesAlgebra.coe_degreeOne] using hc

theorem affineBlowUpZeroPoint_closure (a : I) (ha : (a : R) ≠ 0) :
    closure ({affineBlowUpZeroPoint I a ha} : Set (affineBlowUp I)) = Set.univ := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have h : ProjectiveSpectrum.vanishingIdeal
      ({affineBlowUpZeroPoint I a ha} : Set (affineBlowUp I)) = ⊥ := by
    simp [ProjectiveSpectrum.vanishingIdeal, affineBlowUpZeroPoint]
  rw [h]
  exact ProjectiveSpectrum.zeroLocus_bot _

theorem affineBlowUp_isIntegral_of_ne_bot (hI : I ≠ ⊥) : IsIntegral (affineBlowUp I) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have : IsReduced (affineBlowUp I) := affineBlowUp_isReduced_of_base_reduced I
  have : IrreducibleSpace (affineBlowUp I) := by
    apply (irreducibleSpace_def _).mpr
    simpa only [affineBlowUpZeroPoint_closure I ⟨a, ha⟩ ha0, Set.top_eq_univ] using
      (isIrreducible_singleton (x := affineBlowUpZeroPoint I ⟨a, ha⟩ ha0)).closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem affineBlowUp_exists_effectiveCartier (hI : I ≠ ⊥) :
    let := affineBlowUp_isIntegral_of_ne_bot I hI
    ∃ (E : CartierDivisor (affineBlowUp I)) (hE : E.IsEffective),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal I := by
  let := affineBlowUp_isIntegral_of_ne_bot I hI
  exact exists_effectiveCartier_of_invertibleIdeal _ (affineBlowUp.isInvertible_exceptionalIdeal I)

end MixedFujita
