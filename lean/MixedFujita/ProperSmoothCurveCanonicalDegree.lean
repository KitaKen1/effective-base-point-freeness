/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CurveCanonicalWeilComparison
public import MixedFujita.ProperCurveSerreVanishing

@[expose] public section
open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurveCanonicalDivisor_degree
    (hX : topologicalKrullDim X = 1) (c₀ : EtaleChart K X 1) :
    properCurveCartierDegree (K := K) hX (smoothCanonicalDivisor c₀) =
      2 * (Module.finrank K (Scheme.Modules.Cohomology
        (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 1 _
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  let : ∀ x : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := fun x =>
    smoothOverField_codimensionOne_stalk_DVR (K := K) x
  let : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (X ↘ Spec (CommRingCat.of K))]
    infer_instance⟩
  have hdim (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hX.le
  have hex : ValuativeCriterion.Existence (X ↘ Spec (CommRingCat.of K)) := by
    have h := UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (CommRingCat.of K)))
    exact h.1
  have hF := (isFunctionField_functionField_iff K).mpr hX
  have hk := algebraicallyClosedField_isIntegrallyClosedIn K X.functionField
  have hc := smoothCurveCanonicalDivisor_canonicalClass hex hdim hF hk hX c₀
  have hd := SchemeWeilDivisor.relativeDegree_eq_two_mul_genus_sub_two hex hdim hF hk hc
  have hz : Module.finrank K (Scheme.Modules.Cohomology (0 : CartierDivisor X).sheaf 1) =
      Module.finrank K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) := by
    exact Scheme.Modules.finrank_cohomology_congr K
      ((CartierDivisor.sheafIsoToWeilDivisor hdim 0) ≪≫
        eqToIso (by rw [← CartierDivisor.toWeilDivisorHom_apply, map_zero]) ≪≫
        SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1
  change CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) _ = _
  rw [CartierDivisor.relativeDegree_apply, hd, Scheme.genus_def, hz]

end MixedFujita