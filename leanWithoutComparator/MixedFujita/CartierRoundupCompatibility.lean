/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NormalCartierCoefficientExt
public import MixedFujita.CrepantDiscrepancyComposition
public import MixedFujita.BasePrimeCartierLattice

/-! Coefficientwise rounding uniquely determines an actual Cartier divisor
on a normal scheme. Relative canonical divisors satisfy an exact cocycle,
so the unrounded boundary transforms agree before any rounding is performed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem cartier_roundup_unique
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (B Q Q' : CartierDivisor X) (d : ℕ)
    (hQ : ∀ t : CodimensionOnePoint X, cartierCoefficient Q (t : X) =
      ⌈-((cartierCoefficient B (t : X) : ℝ) / (d : ℝ))⌉)
    (hQ' : ∀ t : CodimensionOnePoint X, cartierCoefficient Q' (t : X) =
      ⌈-((cartierCoefficient B (t : X) : ℝ) / (d : ℝ))⌉) : Q = Q' :=
  cartierDivisor_eq_of_forall_coefficient_eq hnorm Q Q' (fun t => (hQ t).trans (hQ' t).symm)

theorem cartier_roundup_unique_of_boundary_eq
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (B B' Q Q' : CartierDivisor X) (d : ℕ) (hB : B = B')
    (hQ : ∀ t : CodimensionOnePoint X, cartierCoefficient Q (t : X) =
      ⌈-((cartierCoefficient B (t : X) : ℝ) / (d : ℝ))⌉)
    (hQ' : ∀ t : CodimensionOnePoint X, cartierCoefficient Q' (t : X) =
      ⌈-((cartierCoefficient B' (t : X) : ℝ) / (d : ℝ))⌉) : Q = Q' := by
  subst B'
  exact cartier_roundup_unique hnorm B Q Q' d hQ hQ'

section Tower
variable {K : Type u} [Field K] {n : ℕ} {X T Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral Y]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  (ρ : T ⟶ X) (σ : Y ⟶ T) [IsDominant ρ] [IsDominant σ]
  [ρ.IsOver (Spec (.of K))] [σ.IsOver (Spec (.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
  (cX : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
  (cT : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
  (cY : EtaleChart K Y n) (hY : iSup (fun c : EtaleChart K Y n => c.U) = ⊤)

theorem birationalRelativeCanonicalDivisor_comp :
    birationalRelativeCanonicalDivisor n (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) cX hX cY hY =
    cartierPullback σ (birationalRelativeCanonicalDivisor n ρ hρ cX hX cT hT) +
      birationalRelativeCanonicalDivisor n σ hσ cT hT cY hY := by
  have hu : (isUnit_chartRelativeJacobianDet_of_bijective (σ ≫ ρ)
      (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) cX cY).unit =
      Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom
        (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ cX cT).unit *
      (isUnit_chartRelativeJacobianDet_of_bijective σ hσ cT cY).unit := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul, Units.coe_map]
    exact chartRelativeJacobianDet_comp ρ σ cX cT cY
  unfold birationalRelativeCanonicalDivisor relativeCanonicalDivisor
  rw [hu, principalCartierDivisor_mul, cartierPullback_add, cartierPullback_sub,
    cartierPullback_principal, cartierPullback_comp]
  abel

theorem relativeCanonical_boundary_transform_comp (B : CartierDivisor X) (d : ℕ) :
    cartierPullback σ (cartierPullback ρ B - (d : ℤ) •
      birationalRelativeCanonicalDivisor n ρ hρ cX hX cT hT) - (d : ℤ) •
      birationalRelativeCanonicalDivisor n σ hσ cT hT cY hY =
    cartierPullback (σ ≫ ρ) B - (d : ℤ) •
      birationalRelativeCanonicalDivisor n (σ ≫ ρ)
        (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) cX hX cY hY := by
  rw [birationalRelativeCanonicalDivisor_comp ρ σ hρ hσ cX hX cT hT cY hY,
    cartierPullback_sub, cartierPullback_zsmul, cartierPullback_comp, smul_add]
  abel

theorem relativeCanonical_roundup_transform_comp [IsLocallyNoetherian Y]
    (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (B : CartierDivisor X) (d : ℕ) (Qiter Qcomp : CartierDivisor Y)
    (hiter : ∀ t : CodimensionOnePoint Y, cartierCoefficient Qiter (t : Y) =
      ⌈-((cartierCoefficient
        (cartierPullback σ (cartierPullback ρ B - (d : ℤ) •
          birationalRelativeCanonicalDivisor n ρ hρ cX hX cT hT) - (d : ℤ) •
          birationalRelativeCanonicalDivisor n σ hσ cT hT cY hY) (t : Y) : ℝ) / (d : ℝ))⌉)
    (hcomp : ∀ t : CodimensionOnePoint Y, cartierCoefficient Qcomp (t : Y) =
      ⌈-((cartierCoefficient
        (cartierPullback (σ ≫ ρ) B - (d : ℤ) •
          birationalRelativeCanonicalDivisor n (σ ≫ ρ)
            (dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ) cX hX cY hY)
        (t : Y) : ℝ) / (d : ℝ))⌉) : Qiter = Qcomp := by
  exact cartier_roundup_unique_of_boundary_eq hnorm _ _ Qiter Qcomp d
    (relativeCanonical_boundary_transform_comp ρ σ hρ hσ cX hX cT hT cY hY B d)
    hiter hcomp

end Tower
end MixedFujita
