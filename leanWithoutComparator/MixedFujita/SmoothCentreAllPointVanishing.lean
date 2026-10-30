/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalBlowupOffCentreVanishing

/-! All-point local vanishing on the blow-up of the actual stalk ideal.
Coordinate ideals are eliminated using their proved equality with the stalk
ideal. The off-center case is an affine vanishing argument. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme CoordinateSubspace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of K)) (n r : ℕ) [SmoothOfRelativeDimension n f]
  (Z : X.IdealSheafData) [SmoothOfRelativeDimension (n - (r + 1)) (Z.subschemeι ≫ f)]

include f

omit [IsLocallyNoetherian X] in
theorem smoothCentre_stalkIdeal_ne_bot (hrn : r + 1 ≤ n) (x : X) : Z.stalkIdeal x ≠ ⊥ := by
  classical
  by_cases hx : x ∈ Z.support
  · obtain ⟨φ, hφ, hI, _, _⟩ :=
      smoothCentre_exists_flat_stalk_coordinates f n (r + 1) Z hrn x hx
    rw [← hI]
    exact coordinateBaseChanged_center_ne_bot K n (r + 1) hrn φ (Nat.zero_lt_succ _) hφ
  · rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support Z hx]
    exact top_ne_bot

set_option maxHeartbeats 1000000 in
theorem smoothCentre_allPoint_local_exceptional_combination_vanish
    [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ]
    (hrn : r + 1 ≤ n) (E : CartierDivisor Z.blowUp) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = Z.exceptionalDivisor)
    (Q : CartierDivisor X) (C : CartierDivisor Z.blowUp) (j : ℕ) (hj : j ≤ r)
    (hC : C = cartierPullback Z.blowUpπ Q + j • E) (x : X) :
    let := affineBlowUp_isIntegral_of_ne_bot (Z.stalkIdeal x)
      (smoothCentre_stalkIdeal_ne_bot f n r Z hrn x)
    ∃ (τ : affineBlowUp (Z.stalkIdeal x) ⟶ Z.blowUp) (hτ : IsDominant τ),
      let := hτ
      IsPullback τ (affineBlowUp.π (Z.stalkIdeal x)) Z.blowUpπ (X.fromSpecStalk x) ∧
      ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology (cartierPullback τ C).sheaf (q + 1)) := by
  classical
  let := affineBlowUp_isIntegral_of_ne_bot (Z.stalkIdeal x)
    (smoothCentre_stalkIdeal_ne_bot f n r Z hrn x)
  dsimp only
  by_cases hx : x ∈ Z.support
  · obtain ⟨φ, hφ, hI, hlocal⟩ :=
      smoothCentre_local_exceptional_combination_vanish f n r Z hrn E hE hEI Q C j hj hC x hx
    have hsimple : ∃ hne : (centerIdeal K n (r + 1)).map φ ≠ ⊥,
        let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal K n (r + 1)).map φ) hne
        ∃ (τ : affineBlowUp ((centerIdeal K n (r + 1)).map φ) ⟶ Z.blowUp)
          (hτ : IsDominant τ),
          let := hτ
          IsPullback τ (affineBlowUp.π ((centerIdeal K n (r + 1)).map φ))
            Z.blowUpπ (X.fromSpecStalk x) ∧
          ∀ q : ℕ, Subsingleton
            (Scheme.Modules.Cohomology (cartierPullback τ C).sheaf (q + 1)) := by
      refine ⟨coordinateBaseChanged_center_ne_bot K n (r + 1) hrn φ (Nat.zero_lt_succ _) hφ, ?_⟩
      obtain ⟨τ, hτ, H, _, hv⟩ := hlocal
      exact ⟨τ, hτ, H, hv⟩
    rw [hI] at hsimple
    obtain ⟨_, hsimple⟩ := hsimple
    exact hsimple
  · obtain ⟨τ, H⟩ := exists_isPullback_fromSpecStalk Z x
    let : Flat τ := flat_of_isPullback_fromSpecStalk H
    let hτ : IsDominant τ := flat_nonempty_isDominant τ
    exact ⟨τ, hτ, H, fun q ↦ localBlowUp_cartier_vanish_off_center Z x hx _ q⟩

end MixedFujita
