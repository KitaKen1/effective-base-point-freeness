/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperSmoothCurveCanonicalDegree
public import MixedFujita.ProperCurveBigDegree
public import MixedFujita.ProperCurveNumericalTriviality
public import MixedFujita.CartierSectionPrimeDecomposition
public import MixedFujita.KawamataViehwegStatement
public import MixedFujita.SNCModuliUniformSectionBoundsModel

/-! The original SNC and sum forms of Kawamata--Viehweg vanishing in dimension one.
The original boundary, bigness, cohomology and canonical-divisor definitions are retained. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section CurveDegree
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
  [Smooth (X ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurve_degree_nonneg_of_nef
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X) (hD : CartierIsNef K D) :
    0 ≤ properCurveCartierDegree (K := K) hX D := by
  rw [← cartierCurvePullbackDegree_id (K := K) hX D]
  exact hD X hX (𝟙 X) (Category.id_comp _)

omit [Smooth (X ↘ Spec (CommRingCat.of K))] in
theorem properSmoothCurve_boundary_degree_nonneg [IsLocallyNoetherian X]
    (hX : topologicalKrullDim X = 1) {r : ℕ} (E : Fin r → CartierDivisor X)
    (hE : ∀ k (x : CodimensionOnePoint X), 0 ≤ cartierCoefficient (E k) (x : X))
    (a : Fin r → ℕ) :
    0 ≤ properCurveCartierDegree (K := K) hX (∑ k, a k • E k) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hdeg (k : Fin r) : 0 ≤ properCurveCartierDegree (K := K) hX (E k) := by
    change 0 ≤ CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) _
    rw [CartierDivisor.relativeDegree_apply]
    apply SchemeWeilDivisor.relativeDegree_nonneg
    apply (WeilDivisor.isEffective_iff _).mpr
    intro x
    rw [cartier_toWeilDivisor_coeff_eq_cartierCoefficient]
    exact hE k x
  change 0 ≤ CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) _
  rw [map_sum]
  exact Finset.sum_nonneg fun k _ => by
    rw [map_nsmul, nsmul_eq_mul]
    exact mul_nonneg (Int.natCast_nonneg _) (hdeg k)

end CurveDegree

section AdjointVanishing
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurve_cohomology_subsingleton_of_adjoint_degree_positive
    (hX : topologicalKrullDim X = 1) (c₀ : EtaleChart K X 1)
    (Q B : CartierDivisor X) (m : ℕ) (hm : 1 ≤ m)
    (hB : 0 ≤ properCurveCartierDegree (K := K) hX B)
    (hpos : 0 < properCurveCartierDegree (K := K) hX
      (m • (Q - smoothCanonicalDivisor c₀) - B)) (q : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology Q.sheaf (q + 1)) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 1 _
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  apply properSmoothCurve_cohomology_subsingleton_of_degree_gt_two_genus_sub_two_isAlgClosed (K := K) hX Q
  rw [← properSmoothCurveCanonicalDivisor_degree hX c₀]
  change 0 < CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))
    (m • (Q - smoothCanonicalDivisor c₀) - B) at hpos
  rw [map_sub, map_nsmul, map_sub, nsmul_eq_mul] at hpos
  have hm' : (0 : ℤ) < m := by omega
  change 0 < (m : ℤ) * (properCurveCartierDegree (K := K) hX Q -
    properCurveCartierDegree (K := K) hX (smoothCanonicalDivisor c₀)) -
      properCurveCartierDegree (K := K) hX B at hpos
  nlinarith

end AdjointVanishing

/-- The exact original SNC vanishing proposition is proved in dimension one. -/
theorem kawamataViehwegVanishingSNC_curve
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] :
    KawamataViehwegVanishingSNC K 1 := by
  classical
  intro X _ _ _ _ _ c₀ r ξ _ _ _ E hEc Q m hm a _ _ hbig
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 1 _
  have hX : topologicalKrullDim X = 1 :=
    geometricDimension_eq_of_smooth_relativeDimension (k := 1) (X ↘ Spec (CommRingCat.of K))
  have hB := properSmoothCurve_boundary_degree_nonneg (K := K) hX E (fun k x => by
    rw [hEc]; split_ifs <;> norm_num) a
  have hpos := properSmoothCurve_degree_pos_of_isBig (K := K) hX _ hbig
  exact properSmoothCurve_cohomology_subsingleton_of_adjoint_degree_positive hX c₀ Q _ m hm
    hB hpos 0

/-- The exact original sum proposition is proved directly by intrinsic curve degrees. -/
theorem kawamataViehwegVanishingSNCSum_curve
    (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] :
    KawamataViehwegVanishingSNCSum K 1 := by
  classical
  intro X _ _ _ _ _ c₀ r ξ _ _ _ E hEc Q m hm a _ D₁ D₂ heq _ hbig hnef
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 1 _
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hX : topologicalKrullDim X = 1 :=
    geometricDimension_eq_of_smooth_relativeDimension (k := 1) (X ↘ Spec (CommRingCat.of K))
  have hB := properSmoothCurve_boundary_degree_nonneg (K := K) hX E (fun k x => by
    rw [hEc]; split_ifs <;> norm_num) a
  have hD₁ := properSmoothCurve_degree_pos_of_isBig (K := K) hX D₁ hbig
  have hD₂ := properSmoothCurve_degree_nonneg_of_nef (K := K) hX D₂ hnef
  have hpos : 0 < properCurveCartierDegree (K := K) hX
      (m • (Q - smoothCanonicalDivisor c₀) - ∑ k, a k • E k) := by
    rw [heq, properCurveCartierDegree_add]
    omega
  exact properSmoothCurve_cohomology_subsingleton_of_adjoint_degree_positive hX c₀ Q _ m hm
    hB hpos 0

end MixedFujita