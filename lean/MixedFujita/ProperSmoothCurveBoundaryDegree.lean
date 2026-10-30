/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperSmoothCurveKawamataViehwegVanishing
public import MixedFujita.KltPairs

/-! 元の有効境界から曲線標準次数の下界。 See reports/check-214-curve-f1-f2-integration.json for the verified scope. -/

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


theorem properSmoothCurve_boundaryNumerator_degree_ge_canonical
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K))]
    (hX : topologicalKrullDim X = 1) (c₀ : EtaleChart K X 1)
    (f₀ : X.functionFieldˣ) (r : ℕ) (D' : CartierDivisor X)
    (heff : LogPairBoundaryEffective c₀ f₀ r D') :
    (r : ℤ) * (2 * (Module.finrank K (Scheme.Modules.Cohomology
      (0 : CartierDivisor X).sheaf 1) : ℤ) - 2) ≤
      properCurveCartierDegree (K := K) hX D' := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth 1 _
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  let B := D' - r • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀)
  have hcoef (z : CodimensionOnePoint X) : 0 ≤ cartierCoefficient B (z : X) := by
    obtain ⟨c, hc⟩ := Opens.mem_iSup.mp
      ((etaleCharts_cover (K := K) (X := X) (n := 1)).symm ▸ Opens.mem_top (z : X))
    have hlocal : (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀).IsLocalEquationAt
        (z : X) (f₀ * etaleChartCanonicalEquation c₀ c) := by
      rw [add_comm]
      exact (CartierDivisor.isLocalEquationAt_principalCartierDivisor (z : X) f₀).mul
        (canonicalDivisor_isLocalEquationAt c₀ etaleCharts_cover c hc)
    dsimp only [B]
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, cartierCoefficient_eq_ord hlocal]
    exact sub_nonneg.mpr (heff c (z : X) hc z.property)
  have hb : 0 ≤ properCurveCartierDegree (K := K) hX B := by
    change 0 ≤ CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K)) B
    rw [CartierDivisor.relativeDegree_apply]
    apply SchemeWeilDivisor.relativeDegree_nonneg
    apply (WeilDivisor.isEffective_iff _).mpr
    intro z
    rw [cartier_toWeilDivisor_coeff_eq_cartierCoefficient]
    exact hcoef z
  change 0 ≤ CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))
    (D' - r • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀)) at hb
  rw [map_sub, map_nsmul, map_add, nsmul_eq_mul] at hb
  change 0 ≤ properCurveCartierDegree (K := K) hX D' - (r : ℤ) *
    (properCurveCartierDegree (K := K) hX (smoothCanonicalDivisor c₀) +
      properCurveCartierDegree (K := K) hX (principalCartierDivisor X f₀)) at hb
  rw [properSmoothCurveCanonicalDivisor_degree hX c₀,
    properSmoothCurve_principalCartierDegree_zero hX f₀, add_zero] at hb
  omega

end MixedFujita
