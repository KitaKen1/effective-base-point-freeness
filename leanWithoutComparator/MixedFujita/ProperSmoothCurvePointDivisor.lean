/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedPointResidueDegree
public import MixedFujita.CurveCartierSerreDuality
public import MixedFujita.NormalCartierEffectivity
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.CartierSectionPrimeDecomposition
public import MixedFujita.GeometricSmoothTaylor

/-! 実閉点の次数1有効Cartier因子。 See reports/check-214-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [Smooth (X ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurve_exists_degree_one_point_divisor
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : IsNoetherian X := properOverField_scheme_isNoetherian (K := K) (X := X)
    ∃ E : CartierDivisor X, E.IsEffective ∧
      properCurveCartierDegree (K := K) hX E = 1 ∧
      ∀ z : CodimensionOnePoint X,
        cartierCoefficient E (z : X) = if (z : X) = x then 1 else 0 := by
  classical
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  letI : ∀ z : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := fun z =>
    smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have hdim (z : X) : coheight z ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim z).trans hX.le
  have hx1 : coheight x = 1 := by
    have h := geometricSmoothScheme_closedPoint_stalk_dimension (K := K) 1 hX x hx
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact_mod_cast h
  let ξ : CodimensionOnePoint X := ⟨x, hx1⟩
  let E : CartierDivisor X := SchemeWeilDivisor.equivCartierDivisor hdim (WeilDivisor.ofPoint ξ)
  have hEweil : E.toWeilDivisor = WeilDivisor.ofPoint ξ := by
    rw [← SchemeWeilDivisor.equivCartierDivisor_symm_apply hdim]
    exact (SchemeWeilDivisor.equivCartierDivisor hdim).symm_apply_apply _
  have hcoef (z : CodimensionOnePoint X) :
      cartierCoefficient E (z : X) = if (z : X) = x then 1 else 0 := by
    rw [← cartier_toWeilDivisor_coeff_eq_cartierCoefficient, hEweil]
    by_cases hz : (z : X) = x
    · have hzx : z = ξ := Subtype.ext hz
      simp only [hzx, WeilDivisor.coeff_ofPoint_self, ξ, ↓reduceIte]
    · rw [WeilDivisor.coeff_ofPoint_of_ne (fun h => hz (congrArg Subtype.val h)), ite_eq_right hz]
  have hnorm (z : X) : IsIntegrallyClosed (X.presheaf.stalk z) :=
    smooth_stalk_isIntegrallyClosed (K := K) z
  refine ⟨E, (normal_cartier_isEffective_iff_coefficients_nonneg hnorm E).mpr
    (fun z => by rw [hcoef]; split_ifs <;> omega), ?_, hcoef⟩
  change CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) E = 1
  rw [CartierDivisor.relativeDegree_apply, hEweil, SchemeWeilDivisor.relativeDegree_ofPoint,
    finiteTypeOverAlgClosed_residueDegree_eq_one _ x hx]
  rfl

end MixedFujita
