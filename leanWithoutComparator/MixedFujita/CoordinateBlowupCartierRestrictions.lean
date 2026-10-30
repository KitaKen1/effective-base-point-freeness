/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineBlowupIntegralCartier
public import MixedFujita.CoordinateExceptionalProjectiveScheme

/-! Coordinate centers construct the actual effective exceptional Cartier
divisor and its projective exceptional subscheme over the blow-up. Every actual
infinitesimal layer is its negative Cartier restriction, with no supplied divisor
or scheme comparison. Identifying the degree-one restriction with O(1) remains
a separate geometric calculation. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme CohomologyAux CoordinateSubspace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n) (hr : 0 < r)

noncomputable local instance : CommRing (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) :=
  Ideal.Quotient.commRing _

include hrn hr in
theorem coordinateCenterIdeal_ne_bot [Nontrivial A] : centerIdeal A n r ≠ ⊥ := by
  intro h
  have hx := X_mem_centerIdeal A n r (j := ⟨0, lt_of_lt_of_le hr hrn⟩) hr
  rw [h, Ideal.mem_bot] at hx
  exact MvPolynomial.X_ne_zero _ hx

include hrn hr in
theorem coordinateBlowUp_isIntegral [IsDomain A] : IsIntegral (modelBlowUp A n r) :=
  affineBlowUp_isIntegral_of_ne_bot _ (coordinateCenterIdeal_ne_bot A n r hrn hr)

theorem coordinateBlowUp_exists_cartier_projective_restrictions
    [IsDomain A] [IsNoetherianRing A] :
    let := coordinateBlowUp_isIntegral A n r hrn hr
    ∃ (E : CartierDivisor (modelBlowUp A n r)) (hE : E.IsEffective)
      (e : (effectiveCartierIdealSheaf E hE).subscheme ≅
        Proj (MvPolynomial.homogeneousSubmodule (Fin r)
          (MvPolynomial (Fin n) A ⧸ centerIdeal A n r))),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal (centerIdeal A n r) ∧
      e.inv ≫ (effectiveCartierIdealSheaf E hE).subschemeι = projInitial A n r hrn ∧
      ∀ m : ℕ, Nonempty
        (infinitesimalCohomologyLayer (affineBlowUp.π (centerIdeal A n r)) (centerIdeal A n r)
          (unitModule (modelBlowUp A n r)) m ≅
            (Scheme.Modules.pushforward (projInitial A n r hrn)).obj
              ((Scheme.Modules.pullback (projInitial A n r hrn)).obj (-((m + 1) • E)).sheaf)) := by
  let := coordinateBlowUp_isIntegral A n r hrn hr
  obtain ⟨E, hE, hJ⟩ := affineBlowUp_exists_effectiveCartier (centerIdeal A n r)
    (coordinateCenterIdeal_ne_bot A n r hrn hr)
  let e := idealSubschemeIsoOfClosedImmersion (effectiveCartierIdealSheaf E hE)
    (projInitial A n r hrn) ((ker_projInitial A n r hrn).trans hJ.symm)
  have hp : e.inv ≫ (effectiveCartierIdealSheaf E hE).subschemeι = projInitial A n r hrn :=
    idealSubschemeIsoOfClosedImmersion_inv_inclusion _ (projInitial A n r hrn)
      ((ker_projInitial A n r hrn).trans hJ.symm)
  refine ⟨E, hE, e, hJ, hp, ?_⟩
  intro m
  exact ⟨infinitesimalLayerCartierCokernelIso (affineBlowUp.π (centerIdeal A n r))
      (centerIdeal A n r) E hE hJ m ≪≫ cartierIdealPowerCutIso E hE (m + 1) ≪≫
        cartierCutQuotientPushforwardIsoOfSubschemeIso (-((m + 1) • E)) E hE e
          (projInitial A n r hrn) hp⟩

end MixedFujita
