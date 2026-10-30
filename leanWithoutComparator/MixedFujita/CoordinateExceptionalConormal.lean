/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineBlowupReesCartier
public import MixedFujita.CoordinateReesTwistingBundle
public import MixedFujita.CoordinateBlowupCartierRestrictions

/-! The coordinate exceptional divisor has conormal O(1). This is constructed
from the actual ideal generators, with no supplied Cartier or restriction model. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme CohomologyAux CoordinateSubspace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable (A : Type u) [CommRing A] [IsDomain A] (n r : ℕ) (hrn : r ≤ n) (hr : 0 < r)
noncomputable local instance coordinateConormalCenterCommRing :
    CommRing (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) := Ideal.Quotient.commRing _

theorem coordinateBlowUp_exists_cartier_conormal :
    let := coordinateBlowUp_isIntegral A n r hrn hr
    ∃ (E : CartierDivisor (modelBlowUp A n r)) (hE : E.IsEffective),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal (centerIdeal A n r) ∧
      Nonempty ((-E).sheaf ≅ (coordinateReesTwistingBundle A n r hrn).toModules 1) ∧
      Nonempty ((Scheme.Modules.pullback (projInitial A n r hrn)).obj (-E).sheaf ≅
        projectiveSpace.twist (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) 1) := by
  let := coordinateBlowUp_isIntegral A n r hrn hr
  let : Nonempty (ULift.{u} (Fin r)) := ⟨⟨⟨0, hr⟩⟩⟩
  obtain ⟨E, hE, hI, ⟨e⟩⟩ := exists_exceptionalCartier_reesTwisting (centerIdeal A n r)
    (fun i : ULift.{u} (Fin r) => genXOfFin A n r hrn i.down)
    (fun i => MvPolynomial.X_ne_zero _) (coordinateRees_degreeOne_cover A n r hrn)
  refine ⟨E, hE, hI, ⟨e⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.pullback (projInitial A n r hrn)).mapIso e ≪≫
    coordinateReesTwistingModuleRestrictionIso A n r hrn 1

include hr in
theorem coordinateBlowUp_infinitesimal_projective_layers [IsNoetherianRing A] (m : ℕ) :
    Nonempty
      (infinitesimalCohomologyLayer (affineBlowUp.π (centerIdeal A n r)) (centerIdeal A n r)
        (unitModule (modelBlowUp A n r)) m ≅
          (Scheme.Modules.pushforward (projInitial A n r hrn)).obj
            (projectiveSpace.twist (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)
              ((m : ℤ) + 1))) := by
  let := coordinateBlowUp_isIntegral A n r hrn hr
  obtain ⟨E, hE, hI, -, ⟨a⟩⟩ := coordinateBlowUp_exists_cartier_conormal A n r hrn hr
  let e := idealSubschemeIsoOfClosedImmersion (effectiveCartierIdealSheaf E hE)
    (projInitial A n r hrn) ((ker_projInitial A n r hrn).trans hI.symm)
  have hp := idealSubschemeIsoOfClosedImmersion_inv_inclusion (effectiveCartierIdealSheaf E hE)
    (projInitial A n r hrn) ((ker_projInitial A n r hrn).trans hI.symm)
  exact ⟨infinitesimalLayerLineBundlePowerIso (affineBlowUp.π (centerIdeal A n r))
    (centerIdeal A n r) E hE hI e (projInitial A n r hrn) hp
    (projectiveSpace.twistingBundle (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)) a m⟩

theorem coordinateBlowUp_infinitesimal_layer_cohomology_vanish [IsNoetherianRing A]
    (hs : r + 1 ≤ n) (m q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology
      (infinitesimalCohomologyLayer (affineBlowUp.π (centerIdeal A n (r + 1)))
        (centerIdeal A n (r + 1)) (unitModule (modelBlowUp A n (r + 1))) m) (q + 1)) := by
  obtain ⟨e⟩ := coordinateBlowUp_infinitesimal_projective_layers A n (r + 1) hs
    (Nat.zero_lt_succ _) m
  have := actual_projectiveSpace_twist_vanish
    (MvPolynomial (Fin n) A ⧸ centerIdeal A n (r + 1)) r q ((m : ℤ) + 1) (Or.inr (by omega))
  have := (closedImmersionCohomologyAddEquiv (projInitial A n (r + 1) hs)
    (projectiveSpace.twist (Fin (r + 1)) (MvPolynomial (Fin n) A ⧸ centerIdeal A n (r + 1))
      ((m : ℤ) + 1)) (q + 1)).subsingleton
  exact (actualCohomologyLinearEquivOfIso e (q + 1)).subsingleton

/-- Every finite exceptional thickening has vanishing positive structure cohomology. -/
theorem coordinateBlowUp_infinitesimal_quotient_cohomology_vanish [IsNoetherianRing A]
    (hs : r + 1 ≤ n) (m q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology
      ((unitModule (modelBlowUp A n (r + 1))).quotientIdealPow
        (affineBlowUp.π (centerIdeal A n (r + 1))) (centerIdeal A n (r + 1)) m) (q + 1)) := by
  apply quotient_cohomology_vanish_from_layers _ _ _ (q + 1) 0
    (coordinateBlowUp_initial_positive_cohomology_vanish A n r hs q)
    (fun j _ => coordinateBlowUp_infinitesimal_layer_cohomology_vanish A n r hs j q)
    m (Nat.zero_le _)

end MixedFujita
