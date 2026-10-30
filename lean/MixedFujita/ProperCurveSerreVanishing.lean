/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CurveCartierSerreDuality
public import MixedFujita.ProperCartierCohomology

/-!
On a proper smooth integral curve the geometric hypotheses supply the
Noetherian scheme, codimension-one DVRs, all function-field places and the
function-field dimension. One actual Cartier dualizing divisor serves all D.
The condition deg D > 2 dim H1(O) - 2 kills every actual positive cohomology
group. The exact constant-field hypothesis is derived over an algebraically
closed ground field. No projective embedding, ample twist, characteristic
zero, finite-cohomology input or supplied duality is assumed. The comparison
with the existing etale-chart smoothCanonicalDivisor remains separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


section ProperSmoothCurve

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [Smooth (X ↘ Spec (CommRingCat.of K))]

/-- A single actual Cartier dualizing divisor works for every supplied Cartier divisor. -/
theorem properSmoothCurve_exists_cartierSerreDuality
    (hX : topologicalKrullDim X = 1)
    (hk : IsIntegrallyClosedIn K X.functionField) :
    ∃ C : CartierDivisor X,
      properCurveCartierDegree (K := K) hX C =
        2 * (Module.finrank K (Scheme.Modules.Cohomology
          (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 ∧
      ∀ D : CartierDivisor X,
        Nonempty (Module.Dual K (Scheme.Modules.Cohomology D.sheaf 1) ≃ₗ[K]
          Γ((C - D).sheaf, ⊤)) := by
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  letI : ∀ x : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (x : X)) := fun x =>
    smoothOverField_codimensionOne_stalk_DVR (K := K) x
  letI : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from (X ↘ Spec (CommRingCat.of K))]
    infer_instance⟩
  have hdim (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hX.le
  have hex : ValuativeCriterion.Existence (X ↘ Spec (CommRingCat.of K)) := by
    have h := UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (CommRingCat.of K)))
    exact h.1
  have hF := (isFunctionField_functionField_iff K).mpr hX
  refine ⟨curveDualizingCartierDivisor hex hdim hF hk, ?_, fun D =>
    ⟨curveCartierSerreDuality hex hdim hF hk D⟩⟩
  exact curveDualizingCartierDivisor_degree hex hdim hF hk

/-- The sharp degree bound for actual positive cohomology on a proper smooth curve. -/
theorem properSmoothCurve_cohomology_subsingleton_of_degree_gt_two_genus_sub_two
    (hX : topologicalKrullDim X = 1)
    (hk : IsIntegrallyClosedIn K X.functionField) (D : CartierDivisor X)
    (hD : 2 * (Module.finrank K (Scheme.Modules.Cohomology
        (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 <
      properCurveCartierDegree (K := K) hX D) (q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology D.sheaf (q + 1)) := by
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  cases q with
  | zero =>
    change Subsingleton (Scheme.Modules.Cohomology D.sheaf 1)
    letI : Module.Free K (Scheme.Modules.Cohomology D.sheaf 1) := Module.Free.of_divisionRing K (Scheme.Modules.Cohomology D.sheaf 1)
    letI : Module.Projective K (Scheme.Modules.Cohomology D.sheaf 1) := Module.Projective.of_free
    obtain ⟨C, hC, hdual⟩ := properSmoothCurve_exists_cartierSerreDuality hX hk
    obtain ⟨e⟩ := hdual D
    have hneg : properCurveCartierDegree (K := K) hX (C - D) < 0 := by
      change CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) (C - D) < 0
      rw [map_sub]
      change properCurveCartierDegree (K := K) hX C -
        properCurveCartierDegree (K := K) hX D < 0
      rw [hC]
      omega
    letI : Subsingleton Γ((C - D).sheaf, ⊤) :=
      ⟨fun s t => (show s = 0 from by
        by_contra hs
        exact (not_le_of_gt hneg)
          (properSmoothCurveCartierDegree_nonneg_of_nonzero_section hX (C - D) s hs)).trans
        (show t = 0 from by
          by_contra ht
          exact (not_le_of_gt hneg)
            (properSmoothCurveCartierDegree_nonneg_of_nonzero_section hX (C - D) t ht)).symm⟩
    have hdual : Subsingleton (Module.Dual K (Scheme.Modules.Cohomology D.sheaf 1)) :=
      ⟨fun φ ψ => e.injective (Subsingleton.elim (e φ) (e ψ))⟩
    exact (Module.subsingleton_dual_iff K (V := Scheme.Modules.Cohomology D.sheaf 1)).mp hdual
  | succ q =>
    exact actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt D.sheaf _
      (by rw [hX]; exact_mod_cast (show 1 < q + 1 + 1 by omega))

end ProperSmoothCurve

theorem algebraicallyClosedField_isIntegrallyClosedIn
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] :
    IsIntegrallyClosedIn K F := by
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨(algebraMap K F).injective, ?_⟩
  intro x hx
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := K) (K := integralClosure K F)).2 ⟨x, hx⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem properSmoothCurve_cohomology_subsingleton_of_degree_gt_two_genus_sub_two_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Smooth (X ↘ Spec (CommRingCat.of K))]
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : 2 * (Module.finrank K (Scheme.Modules.Cohomology
        (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 <
      properCurveCartierDegree (K := K) hX D) (q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology D.sheaf (q + 1)) :=
  properSmoothCurve_cohomology_subsingleton_of_degree_gt_two_genus_sub_two hX
    (algebraicallyClosedField_isIntegrallyClosedIn K X.functionField) D hD q

end MixedFujita
