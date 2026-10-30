/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperSmoothCurveGlobalGeneration
public import MixedFujita.NormalCurveSmoothness
public import MixedFujita.ProperSmoothCurveBoundaryDegree
public import MixedFujita.LinearEffectiveFreenessStatement

/-! 元の正規曲線F2をm≥a+1へ強化して証明。 See reports/check-214-curve-f1-f2-integration.json for the verified scope. -/

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


theorem linearEffectiveFreeness_normalCurve
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (hX : topologicalKrullDim X = 1)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hproj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (c₀ : EtaleChart K X 1) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (D : CartierDivisor X) (hnef : CartierIsNef K D) (a : ℕ)
    (hbig : CartierIsBig K ((r * a) • D - D'))
    (m : ℕ) (hm : a + 1 ≤ m) : CartierIsGloballyGenerated (m • D) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := normalCurve_smooth (K := K) hX hnorm
  let : SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of K)) :=
    geometricSmoothScheme_relativeDimension (K := K) 1 hX
  obtain ⟨H, _, _, b, e, _, he, _⟩ := hproj
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper b K
    rw [← he]
    infer_instance
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hbound := properSmoothCurve_boundaryNumerator_degree_ge_canonical
    (K := K) hX c₀ f₀ r D' heff
  have hpos := properSmoothCurve_degree_pos_of_isBig (K := K) hX _ hbig
  have hnonneg := properSmoothCurve_degree_nonneg_of_nef (K := K) hX D hnef
  change 0 < CartierDivisor.relativeDegree (X ↘ Spec (CommRingCat.of K))
    ((r * a) • D - D') at hpos
  rw [map_sub, map_nsmul, nsmul_eq_mul, Nat.cast_mul] at hpos
  change 0 < (r : ℤ) * a * properCurveCartierDegree (K := K) hX D -
    properCurveCartierDegree (K := K) hX D' at hpos
  have hrpos : (0 : ℤ) < r := by omega
  have hadj : 2 * (Module.finrank K (Scheme.Modules.Cohomology
      (0 : CartierDivisor X).sheaf 1) : ℤ) - 2 <
      (a : ℤ) * properCurveCartierDegree (K := K) hX D := by
    nlinarith
  apply properSmoothCurve_globallyGenerated_of_degree_ge_two_genus (K := K) hX
  rw [properCurveCartierDegree_nsmul]
  have hm' : (a : ℤ) + 1 ≤ m := by exact_mod_cast hm
  by_cases hz : properCurveCartierDegree (K := K) hX D = 0
  · rw [hz, mul_zero]
    rw [hz, mul_zero] at hadj
    omega
  · have hd : 1 ≤ properCurveCartierDegree (K := K) hX D := by omega
    nlinarith

end MixedFujita
