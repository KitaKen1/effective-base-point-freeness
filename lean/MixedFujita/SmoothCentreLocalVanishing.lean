/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothCentreStalkCoordinates
public import MixedFujita.RoundupLocalTransport
public import Hironaka.Scheme.Smooth.LocalBlowUpStalk

/-! The actual local square, its dominant maps and coordinate center are
constructed at every point of a smooth center. A bounded exceptional Cartier
combination therefore has vanishing positive cohomology on this local blow-up.
The global decomposition is the remaining input to this general lemma. -/

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
  [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ]

include f

set_option maxHeartbeats 800000 in
theorem smoothCentre_exists_dominant_coordinate_local_square
    (hrn : r + 1 ≤ n) (x : X) (hx : x ∈ Z.support) :
    ∃ (φ : MvPolynomial (Fin n) K →+* X.presheaf.stalk x) (_hφ : φ.Flat),
      (centerIdeal K n (r + 1)).map φ = Z.stalkIdeal x ∧
      (centerIdeal K n (r + 1)).map φ ≠ ⊤ ∧
      Z.comap (X.fromSpecStalk x) = specIdealSheaf ((centerIdeal K n (r + 1)).map φ) ∧
      ∃ τ : affineBlowUp ((centerIdeal K n (r + 1)).map φ) ⟶ Z.blowUp,
        IsPullback τ (affineBlowUp.π ((centerIdeal K n (r + 1)).map φ))
          Z.blowUpπ (X.fromSpecStalk x) ∧
        IsDominant (X.fromSpecStalk x) ∧
        IsDominant (affineBlowUp.π ((centerIdeal K n (r + 1)).map φ)) ∧ IsDominant τ := by
  obtain ⟨φ, hφ, hI, hJ, hZ⟩ := smoothCentre_exists_flat_stalk_coordinates f n (r + 1) Z hrn x hx
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal K n (r + 1)).map φ)
    (coordinateBaseChanged_center_ne_bot K n (r + 1) hrn φ (Nat.zero_lt_succ _) hφ)
  let : Flat (X.fromSpecStalk x) := flat_fromSpecStalk x
  have hB : IsBlowUp (Z.comap (X.fromSpecStalk x))
      (affineBlowUp.π ((centerIdeal K n (r + 1)).map φ)) := by
    rw [hZ]
    exact affineBlowUp.isBlowUp _
  obtain ⟨τ, H⟩ := (Scheme.IdealSheafData.blowUp.isBlowUp Z).exists_isPullback_of_flat
    (X.fromSpecStalk x) hB
  let : Flat τ := flat_of_isPullback_fromSpecStalk H
  let : IsProper Z.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π Z
  let : Surjective Z.blowUpπ := inferInstance
  let : Surjective (affineBlowUp.π ((centerIdeal K n (r + 1)).map φ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) H inferInstance
  exact ⟨φ, hφ, hI, hJ, hZ, τ, H, flat_nonempty_isDominant _, inferInstance,
    flat_nonempty_isDominant τ⟩

set_option maxHeartbeats 1000000 in
theorem smoothCentre_local_exceptional_combination_vanish
    (hrn : r + 1 ≤ n) (E : CartierDivisor Z.blowUp) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = Z.exceptionalDivisor)
    (Q : CartierDivisor X) (C : CartierDivisor Z.blowUp) (j : ℕ) (hj : j ≤ r)
    (hC : C = cartierPullback Z.blowUpπ Q + j • E) (x : X) (hx : x ∈ Z.support) :
    ∃ (φ : MvPolynomial (Fin n) K →+* X.presheaf.stalk x) (hφ : φ.Flat),
      (centerIdeal K n (r + 1)).map φ = Z.stalkIdeal x ∧
      let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal K n (r + 1)).map φ)
        (coordinateBaseChanged_center_ne_bot K n (r + 1) hrn φ (Nat.zero_lt_succ _) hφ)
      ∃ (τ : affineBlowUp ((centerIdeal K n (r + 1)).map φ) ⟶ Z.blowUp)
        (hτ : IsDominant τ),
        let := hτ
        IsPullback τ (affineBlowUp.π ((centerIdeal K n (r + 1)).map φ))
          Z.blowUpπ (X.fromSpecStalk x) ∧
        Nonempty ((Scheme.Modules.pullback
          (coordinateBaseChangedProjectiveImmersion K n (r + 1) hrn φ hφ)).obj
            (cartierPullback τ C).sheaf ≅ projectiveSpace.twist (Fin (r + 1))
              (X.presheaf.stalk x ⧸ (centerIdeal K n (r + 1)).map φ) (-(j : ℤ))) ∧
        ∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology (cartierPullback τ C).sheaf (q + 1)) := by
  obtain ⟨φ, hφ, hI, hJ, hZ, τ, H, hσ, hg, hτ⟩ :=
    smoothCentre_exists_dominant_coordinate_local_square f n r Z hrn x hx
  let := hσ
  let := hg
  let := hτ
  let := affineBlowUp_isIntegral_of_ne_bot ((centerIdeal K n (r + 1)).map φ)
    (coordinateBaseChanged_center_ne_bot K n (r + 1) hrn φ (Nat.zero_lt_succ _) hφ)
  refine ⟨φ, hφ, hI, τ, hτ, H, ?_⟩
  exact coordinateLocal_roundup_pullback_vanish K n r φ hφ hrn hJ Z.blowUpπ
    (X.fromSpecStalk x) τ H.w Z hZ E hE hEI Q C j hj hC

end MixedFujita
