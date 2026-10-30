/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoordinateExceptionalStandardBaseChange

/-! Direct projective cohomology after flat coordinate base change. The actual
exceptional conormal and all infinitesimal layers are standard projective twists
over the target quotient ring, so all finite exceptional thickenings have
vanishing positive structure cohomology. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory CoordinateSubspace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n)
  {S : Type u} [CommRing S] (φ : MvPolynomial (Fin n) A →+* S) (hφ : φ.Flat)
noncomputable local instance coordinateVanishingTargetCommRing :
    CommRing (S ⧸ (centerIdeal A n r).map φ) := Ideal.Quotient.commRing _

noncomputable def coordinateBaseChangedInitialProjectiveQuotientIso [IsNoetherianRing S] :
    (unitModule (affineBlowUp ((centerIdeal A n r).map φ))).quotientIdealPow
      (affineBlowUp.π ((centerIdeal A n r).map φ)) ((centerIdeal A n r).map φ) 0 ≅
      (Scheme.Modules.pushforward (coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ)).obj
        (unitModule _) :=
  affineBlowUpActualExceptionalQuotientIso _ ≪≫
    idealSubschemePushforwardUnitIsoOfKernel _ _
      (coordinateBaseChangedProjectiveImmersion_ker A n r hrn φ hφ)

include hφ in
theorem coordinateBaseChanged_initial_positive_cohomology_vanish [IsNoetherianRing S]
    (hs : r + 1 ≤ n) (q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology
      ((unitModule (affineBlowUp ((centerIdeal A n (r + 1)).map φ))).quotientIdealPow
        (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ)) ((centerIdeal A n (r + 1)).map φ) 0)
      (q + 1)) := by
  let B := S ⧸ (centerIdeal A n (r + 1)).map φ
  let P := polynomialProjectiveScheme (r + 1) B
  have : Subsingleton ((unitModule P).H (q + 1)) :=
    projectiveSpace.H_structureModule_subsingleton B r q
  have : Subsingleton (Scheme.Modules.Cohomology (unitModule P) (q + 1)) :=
    (sgaCohomologyLinearEquiv (unitModule P) (q + 1)).symm.subsingleton
  have := (closedImmersionCohomologyAddEquiv
    (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ) (unitModule P) (q + 1)).subsingleton
  exact (actualCohomologyLinearEquivOfIso
    (coordinateBaseChangedInitialProjectiveQuotientIso A n (r + 1) hs φ hφ) (q + 1)).subsingleton

theorem coordinateBaseChanged_rees_restriction_cohomology_vanish
    (hs : r + 1 ≤ n) (q : ℕ) (d : ℤ) (h : q + 1 ≠ r ∨ -((r : ℤ) + 1) < d) :
    Subsingleton (Scheme.Modules.Cohomology
      ((Scheme.Modules.pushforward (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ)).obj
        ((Scheme.Modules.pullback (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ)).obj
          ((coordinateBaseChangedReesBundle A n (r + 1) hs φ).toModules d))) (q + 1)) := by
  have := actual_projectiveSpace_twist_vanish (S ⧸ (centerIdeal A n (r + 1)).map φ) r q d h
  have := (actualCohomologyLinearEquivOfIso
    (coordinateBaseChangedStandardReesRestrictionIso A n (r + 1) hs φ hφ d) (q + 1)).subsingleton
  exact (closedImmersionCohomologyAddEquiv
    (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ) _ (q + 1)).subsingleton

variable [IsDomain A] [IsDomain S] (hr : 0 < r)

include hr in
theorem coordinateBaseChanged_exists_standard_conormal :
    let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n r).map φ)
      (coordinateBaseChanged_center_ne_bot A n r hrn φ hr hφ)
    ∃ (E : CartierDivisor (affineBlowUp ((centerIdeal A n r).map φ))) (hE : E.IsEffective),
      effectiveCartierIdealSheaf E hE = affineBlowUp.exceptionalIdeal ((centerIdeal A n r).map φ) ∧
      Nonempty
        ((Scheme.Modules.pullback (coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ)).obj
          (-E).sheaf ≅ projectiveSpace.twist (Fin r) (S ⧸ (centerIdeal A n r).map φ) 1) := by
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n r).map φ)
    (coordinateBaseChanged_center_ne_bot A n r hrn φ hr hφ)
  obtain ⟨E, hE, hI, ⟨a⟩, -⟩ := coordinateBaseChanged_exists_cartier_conormal A n r hrn φ hr hφ
  exact ⟨E, hE, hI, ⟨(Scheme.Modules.pullback
    (coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ)).mapIso a ≪≫
      coordinateBaseChangedStandardReesRestrictionIso A n r hrn φ hφ 1⟩⟩

include hr in
theorem coordinateBaseChanged_standard_projective_layers [IsNoetherianRing S] (m : ℕ) :
    Nonempty
      (infinitesimalCohomologyLayer (affineBlowUp.π ((centerIdeal A n r).map φ))
        ((centerIdeal A n r).map φ) (unitModule (affineBlowUp ((centerIdeal A n r).map φ))) m ≅
      (Scheme.Modules.pushforward (coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ)).obj
        (projectiveSpace.twist (Fin r) (S ⧸ (centerIdeal A n r).map φ) ((m : ℤ) + 1))) := by
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal A n r).map φ)
    (coordinateBaseChanged_center_ne_bot A n r hrn φ hr hφ)
  obtain ⟨E, hE, hI, ⟨a⟩⟩ := coordinateBaseChanged_exists_standard_conormal A n r hrn φ hφ hr
  let p := coordinateBaseChangedProjectiveImmersion A n r hrn φ hφ
  let e := idealSubschemeIsoOfClosedImmersion (effectiveCartierIdealSheaf E hE) p
    ((coordinateBaseChangedProjectiveImmersion_ker A n r hrn φ hφ).trans hI.symm)
  have hp := idealSubschemeIsoOfClosedImmersion_inv_inclusion (effectiveCartierIdealSheaf E hE) p
    ((coordinateBaseChangedProjectiveImmersion_ker A n r hrn φ hφ).trans hI.symm)
  exact ⟨infinitesimalLayerLineBundlePowerIso _ _ E hE hI e p hp
    (projectiveSpace.twistingBundle (Fin r) (S ⧸ (centerIdeal A n r).map φ)) a m⟩

include hφ in
theorem coordinateBaseChanged_layer_positive_cohomology_vanish [IsNoetherianRing S]
    (hs : r + 1 ≤ n) (m q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology
      (infinitesimalCohomologyLayer (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ))
        ((centerIdeal A n (r + 1)).map φ)
        (unitModule (affineBlowUp ((centerIdeal A n (r + 1)).map φ))) m) (q + 1)) := by
  obtain ⟨e⟩ := coordinateBaseChanged_standard_projective_layers A n (r + 1) hs φ hφ
    (Nat.zero_lt_succ _) m
  have := actual_projectiveSpace_twist_vanish (S ⧸ (centerIdeal A n (r + 1)).map φ)
    r q ((m : ℤ) + 1) (Or.inr (by omega))
  have := (closedImmersionCohomologyAddEquiv
    (coordinateBaseChangedProjectiveImmersion A n (r + 1) hs φ hφ)
    (projectiveSpace.twist (Fin (r + 1)) (S ⧸ (centerIdeal A n (r + 1)).map φ)
      ((m : ℤ) + 1)) (q + 1)).subsingleton
  exact (actualCohomologyLinearEquivOfIso e (q + 1)).subsingleton

include hφ in
theorem coordinateBaseChanged_quotient_positive_cohomology_vanish [IsNoetherianRing S]
    (hs : r + 1 ≤ n) (m q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology
      ((unitModule (affineBlowUp ((centerIdeal A n (r + 1)).map φ))).quotientIdealPow
        (affineBlowUp.π ((centerIdeal A n (r + 1)).map φ)) ((centerIdeal A n (r + 1)).map φ) m)
      (q + 1)) := by
  apply quotient_cohomology_vanish_from_layers _ _ _ (q + 1) 0
    (coordinateBaseChanged_initial_positive_cohomology_vanish A n r φ hφ hs q)
    (fun j _ => coordinateBaseChanged_layer_positive_cohomology_vanish A n r φ hφ hs j q)
    m (Nat.zero_le _)

end MixedFujita
