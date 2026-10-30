/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SurjectiveQuotientRestrictionOrder
public import MixedFujita.SNCPointDivisorFamily
public import Hironaka.Scheme.Smooth.SubschemeStalk
public import MixedFujita.EtaleChartTaylorCoordinates

/-! 実SNC成分への局所制限から形式座標制限の高次数。 See reports/check-264-critical-snc-restriction-nonlc.json for the verified scope. Large normal weights transfer HIGH coordinate-divisor RESTRICTION order to weighted ambient order, allowing low ordinary-order transverse terms. Actual toric extraction cancels the critical normal boundary contribution against the Jacobian. Actual surjective local quotients lift maximal-ideal powers modulo their principal coordinate kernel, avoiding target completion/quotient isomorphisms. On an actual critical SNC component at a closed point away from other components, HIGH NATURAL ORIGINAL SECTION RESTRICTION order internally constructs an ORIGINAL ambient nonLC point with actual centered charts/completion/weighted extraction. Original LC CENTER to critical SNC COMPONENT order transfer and suitable model/point construction remain separate; full original-center concentration/nonLC iteration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- The ACTUAL reduced SNC component quotient has the chart normal coordinate
as its kernel generator. High local order on that actual component therefore
gives high FORMAL coordinate restriction order, without any target completion
or quotient-coordinate isomorphism input. -/
theorem snc_component_high_order_formal_coordinate_restriction
    {K : Type u} [Field K] [CharZero K] {n r : ℕ} {T : Scheme.{u}}
    [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K T n) (ξ : Fin r → T) (χ : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ χ) (i₀ : Fin r) (k : Fin n) (hχ : χ i₀ = some k)
    (J : T.IdealSheafData) (hJ : J = (sncDivisorFamilyOfPoints ξ).component (ULift.up i₀))
    (z : J.subscheme) (hy : J.subschemeι z ∈ c.U)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (J.subschemeι z)))
      (T.presheaf.stalk (J.subschemeι z)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (he : stalkTaylorExpansion (J.subschemeι z) e
      (etaleChartStalkCoords c (J.subschemeι z) hy (MvPolynomial.X k)) = MvPowerSeries.X k)
    (a : T.presheaf.stalk (J.subschemeι z)) (N : ℕ)
    (horder : (N : ℕ∞) ≤ localAdicOrder (J.subscheme.presheaf.stalk z) ((J.subschemeι.stalkMap z).hom a)) :
    (N : ℕ∞) ≤ (powerSeriesDivisorRestriction k (stalkTaylorExpansion (J.subschemeι z) e a)).order := by
  let normal := etaleChartStalkCoords c (J.subschemeι z) hy (MvPolynomial.X k)
  have hideal : J.stalkIdeal (J.subschemeι z) = Ideal.span {normal} := by
    have hJI := congrArg (fun Q : T.IdealSheafData => Q.stalkIdeal (J.subschemeι z)) hJ
    rw [hJI, sncDivisorFamilyOfPoints_stalk_on_chart c ξ χ hc _ hy i₀, hχ]
    rfl
  have hker : RingHom.ker (J.subschemeι.stalkMap z).hom ≤ Ideal.span {normal} := by
    rw [J.ker_stalkMap_subschemeι z, hideal]
  exact surjective_local_quotient_high_order_coordinate_restriction
    (J.subschemeι.stalkMap z).hom (J.subschemeι.stalkMap_surjective z) e.toRingEquiv k normal he hker a N horder

end MixedFujita
