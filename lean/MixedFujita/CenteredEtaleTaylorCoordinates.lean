/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EtaleChartTaylorCoordinates
public import MixedFujita.ToricExtractionDomination

/-! 中心化済み実chartから未平行移動の完備化座標。 See reports/check-264-critical-snc-restriction-nonlc.json for the verified scope. Large normal weights transfer HIGH coordinate-divisor RESTRICTION order to weighted ambient order, allowing low ordinary-order transverse terms. Actual toric extraction cancels the critical normal boundary contribution against the Jacobian. Actual surjective local quotients lift maximal-ideal powers modulo their principal coordinate kernel, avoiding target completion/quotient isomorphisms. On an actual critical SNC component at a closed point away from other components, HIGH NATURAL ORIGINAL SECTION RESTRICTION order internally constructs an ORIGINAL ambient nonLC point with actual centered charts/completion/weighted extraction. Original LC CENTER to critical SNC COMPONENT order transfer and suitable model/point construction remain separate; full original-center concentration/nonLC iteration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- A chart already centered at a rational point has actual completion
coordinates sending its UNshifted variables to the formal variables. -/
theorem centered_etale_chart_exists_unshifted_taylorCoordinates
    {K : Type u} [Field K] {n : ℕ} {T : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K T n) (y : T) (hy : y ∈ c.U)
    (β : T.presheaf.stalk y →ₐ[K] K)
    (hc : ∀ i, ¬ IsUnit (T.presheaf.germ c.U y hy (c.coords (MvPolynomial.X i)))) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk y)) (T.presheaf.stalk y) ≃ₐ[K]
      MvPowerSeries (Fin n) K,
      ∀ i, stalkTaylorExpansion y e (etaleChartStalkCoords c y hy (MvPolynomial.X i)) = MvPowerSeries.X i := by
  obtain ⟨e, he, _⟩ := etaleChart_exists_taylorCoordinates c y hy β
  refine ⟨e, fun i => ?_⟩
  have hzero : rationalAffineGermPoint y hy β (c.coords (MvPolynomial.X i)) = 0 :=
    not_not.mp ((rationalLocalPoint_isUnit_iff β _).not.mp (hc i))
  have hi := he i
  rw [etaleChartCenteredStalkCoords_variable, hzero, map_zero, sub_zero] at hi
  exact hi

end MixedFujita
