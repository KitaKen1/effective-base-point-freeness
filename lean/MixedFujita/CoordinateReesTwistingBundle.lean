/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjTwistingPullback
public import MixedFujita.CoordinateExceptionalProjectiveScheme

/-! The actual Rees twisting bundle on a coordinate-center blow-up restricts
under its constructed exceptional projective immersion to the standard O(1).
All integer module twists are identified, over any coefficient ring. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Graded
open CoordinateSubspace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n)

noncomputable local instance coordinateReesCenterCommRing :
    CommRing (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) :=
  Ideal.Quotient.commRing _

theorem coordinateRees_degreeOne_cover :
    ⨆ i : ULift.{u} (Fin r), Proj.basicOpen (reesAlgebra.grading (centerIdeal A n r))
      (reesAlgebra.degreeOne (centerIdeal A n r) (genXOfFin A n r hrn i.down)) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨⟨y, hy⟩, hx⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq
    (centerIdeal A n r) (MvPolynomial.X '' center n r) rfl x
  obtain ⟨j, hj, rfl⟩ := hy
  refine Opens.mem_iSup.mpr ⟨⟨⟨j.val, hj⟩⟩, ?_⟩
  simpa only [affineBlowUp.opensRange_chart, genXOfFin] using hx

noncomputable def coordinateReesTwistingBundle : (modelBlowUp A n r).LineBundle :=
  Proj.twistingSheaf (reesAlgebra.grading (centerIdeal A n r))
    (fun i : ULift.{u} (Fin r) => reesAlgebra.degreeOne (centerIdeal A n r)
      (genXOfFin A n r hrn i.down))
    (fun i => reesAlgebra.degreeOne_mem (genXOfFin A n r hrn i.down))
    (coordinateRees_degreeOne_cover A n r hrn)

theorem coordinateReesTwistingBundle_pullback :
    (coordinateReesTwistingBundle A n r hrn).pullback (projInitial A n r hrn) =
      projectiveSpace.twistingBundle (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) := by
  unfold coordinateReesTwistingBundle projInitial
  rw [projTwistingSheaf_pullback]
  congr 1
  funext i
  exact reesInitial_degreeOne_genX A n r hrn _ i.down.2

noncomputable def coordinateReesTwistingModuleRestrictionIso (d : ℤ) :
    (Scheme.Modules.pullback (projInitial A n r hrn)).obj
        ((coordinateReesTwistingBundle A n r hrn).toModules d) ≅
      projectiveSpace.twist (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) d :=
  sgaLineBundlePullbackPowerIso _ _ d ≪≫
    eqToIso (congrArg (fun L => L.toModules d) (coordinateReesTwistingBundle_pullback A n r hrn))

open TauCeti.AlgebraicGeometry

/-- The standard projective bound now applies to actual restrictions of the
constructed Rees twisting modules, without a supplied restriction isomorphism. -/
theorem coordinateRees_restriction_cohomology_vanish (hs : r + 1 ≤ n) (q : ℕ) (d : ℤ)
    (h : q + 1 ≠ r ∨ -((r : ℤ) + 1) < d) :
    Subsingleton (Scheme.Modules.Cohomology
      ((Scheme.Modules.pushforward (projInitial A n (r + 1) hs)).obj
        ((Scheme.Modules.pullback (projInitial A n (r + 1) hs)).obj
          ((coordinateReesTwistingBundle A n (r + 1) hs).toModules d))) (q + 1)) := by
  have := actual_projectiveSpace_twist_vanish
    (MvPolynomial (Fin n) A ⧸ centerIdeal A n (r + 1)) r q d h
  have := (actualCohomologyLinearEquivOfIso
    (coordinateReesTwistingModuleRestrictionIso A n (r + 1) hs d) (q + 1)).subsingleton
  exact (closedImmersionCohomologyAddEquiv (projInitial A n (r + 1) hs) _ (q + 1)).subsingleton

end MixedFujita
