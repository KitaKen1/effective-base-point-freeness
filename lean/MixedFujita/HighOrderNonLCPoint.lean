/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.KltBoundaryFreeNumericalStart
public import MixedFujita.KltNonproperBirationalTests
public import MixedFujita.LogCanonicalNonproperBirationalTests
public import MixedFujita.FiniteTypeClosedPointEvaluation

/-! 高次数実正則方程式から元点別非lc・非klt障害。 See reports/check-253-singular-concentration-nonLC-point.json for the verified scope. Actual etale chart completions evaluate original global Cartier sections on a possibly singular integral source, without global smoothness. Original normal klt BPF data with positive numerical dimension construct all-high-power concentrated effective divisors at smooth closed points, without an initial L section or KV. Actual high regular-equation order obstructs the original all-model pointwise log-canonical and klt predicates. A boundary-free closed point in any nonempty open and effective non-lc perturbations are constructed internally. Initial and restricted nonvanishing, lc-threshold ample preservation, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower


/-- At a boundary-free chart point, an actual divisor with regular local
order greater than n*d*j destroys the ORIGINAL all-model pointwise log-canonical predicate
at coefficient 1/(j*d). The extraction and discrepancy bound are internal. -/
theorem high_order_regular_equation_not_logCanonical_over_boundary_free_point
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (hn : 1 ≤ n) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (x : X) (hx : x ∈ c.U)
    (hclosed : IsClosed {x}) (hD : D.IsLocalEquationAt x (f ^ d))
    (j : ℕ) (hj : 1 ≤ j) (M : CartierDivisor X) (g : X.functionFieldˣ)
    (z : X.presheaf.stalk x) (hz : z ≠ 0)
    (himage : algebraMap (X.presheaf.stalk x) X.functionField z = (g : X.functionField))
    (hlocal : M.IsLocalEquationAt x g)
    (horder : ((n * d * j : ℕ) : ℕ∞) < localAdicOrder (X.presheaf.stalk x) z) :
    ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M) := by
  intro hklt
  obtain ⟨β⟩ := finiteTypeScheme_closedPoint_has_localEvaluation (K := K) x hclosed
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hec, hσe, hJ⟩ :=
    exists_extraction_prime_at_chart_rational_point hn c x hx β
  have hA := logDiscrepancyDivisor_coefficient_of_local_boundary_zero σ hσ c f d D
    cU e hec (by simpa only [hσe] using hD)
  rw [hJ] at hA
  have hbound := logPairIsLogCanonicalOverBasePoint_discrepancy_bound_on_birational_test
    (𝟙 X) x c f (j * d) (by nlinarith) (j • D + M) hklt σ hσ cU ⟨e, he⟩ (by
      change x ∈ closure ({σ e} : Set X)
      rw [hσe]
      exact subset_closure (Set.mem_singleton x))
  subst x
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : IsDiscreteValuationRing (U.presheaf.stalk e) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) (⟨e, he⟩ : CodimensionOnePoint U)
  have himageU : ((Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom g : U.functionFieldˣ) :
      U.functionField) = algebraMap (U.presheaf.stalk e) U.functionField (σ.stalkMap e z) := by
    rw [← dominantFunctionFieldMap_algebraMap, himage]
    rfl
  have hne : σ.stalkMap e z ≠ 0 := by
    intro hzero
    have hunit : algebraMap (U.presheaf.stalk e) U.functionField (σ.stalkMap e z) ≠ 0 := by
      rw [← himageU]
      exact Units.ne_zero _
    exact hunit (by rw [hzero, map_zero])
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (fun h => hne ((localAdicOrder_eq_top_iff _).mp h))
  have hcoef : cartierCoefficient (cartierPullback σ M) e = (m : ℤ) := by
    rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt σ M e hlocal), himageU,
      scheme_ord_regular_eq_localAdicOrder_nat (⟨e, he⟩ : CodimensionOnePoint U) _ hne m hm.symm]
  have hle := scheme_stalkMap_localAdicOrder_le σ e z
  rw [← hm] at hle
  have hmgt : n * d * j < m := by exact_mod_cast horder.trans_le hle
  have hdisc : logDiscrepancyDivisor n σ hσ c f (j * d) (j • D + M) cU etaleCharts_cover =
      j • logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover - cartierPullback σ M := by
    unfold logDiscrepancyDivisor
    rw [cartierPullback_add, cartierPullback_nsmul]
    module
  rw [hdisc, cartierCoefficient_sub, cartierCoefficient_nsmul, hA, hcoef] at hbound
  have hmgtZ : (n : ℤ) * d * j < m := by exact_mod_cast hmgt
  push_cast at hbound
  nlinarith


/-- At a boundary-free chart point, an actual divisor with regular local
order greater than n*d*j destroys the ORIGINAL all-model pointwise klt predicate
at coefficient 1/(j*d). The extraction and discrepancy bound are internal. -/
theorem high_order_regular_equation_not_klt_over_boundary_free_point
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (hn : 1 ≤ n) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (x : X) (hx : x ∈ c.U)
    (hclosed : IsClosed {x}) (hD : D.IsLocalEquationAt x (f ^ d))
    (j : ℕ) (hj : 1 ≤ j) (M : CartierDivisor X) (g : X.functionFieldˣ)
    (z : X.presheaf.stalk x) (hz : z ≠ 0)
    (himage : algebraMap (X.presheaf.stalk x) X.functionField z = (g : X.functionField))
    (hlocal : M.IsLocalEquationAt x g)
    (horder : ((n * d * j : ℕ) : ℕ∞) < localAdicOrder (X.presheaf.stalk x) z) :
    ¬ LogPairIsKltOverBasePoint (𝟙 X) x c f (j * d) (j • D + M) := by
  intro hklt
  apply high_order_regular_equation_not_logCanonical_over_boundary_free_point hn c f d hd D x hx
    hclosed hD j hj M g z hz himage hlocal horder
  exact logPairIsKltOverBasePoint_logCanonical (𝟙 X) x c f (j * d) (j • D + M) hklt

end MixedFujita
