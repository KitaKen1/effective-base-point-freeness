/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoordinateRestrictionLargeNormalWeight
public import MixedFujita.ToricExtractionDomination
public import MixedFujita.CrepantDiscrepancyComposition
public import MixedFujita.LogCanonicalNonproperBirationalTests
public import MixedFujita.PointClosureHyperplaneRestriction

/-! 実重み付き抽出の法線discrepancy相殺から元ambient非lc。 See reports/check-264-critical-snc-restriction-nonlc.json for the verified scope. Large normal weights transfer HIGH coordinate-divisor RESTRICTION order to weighted ambient order, allowing low ordinary-order transverse terms. Actual toric extraction cancels the critical normal boundary contribution against the Jacobian. Actual surjective local quotients lift maximal-ideal powers modulo their principal coordinate kernel, avoiding target completion/quotient isomorphisms. On an actual critical SNC component at a closed point away from other components, HIGH NATURAL ORIGINAL SECTION RESTRICTION order internally constructs an ORIGINAL ambient nonLC point with actual centered charts/completion/weighted extraction. Original LC CENTER to critical SNC COMPONENT order transfer and suitable model/point construction remain separate; full original-center concentration/nonLC iteration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- High actual FORMAL restriction order along one coefficient-d SNC component
constructs a genuine weighted extraction contradicting the ORIGINAL all-model
pointwise lc predicate. Low ordinary-order transverse terms are allowed.
The original-center-to-this-formal-restriction comparison is a separate step. -/
theorem high_coordinate_restriction_order_not_logCanonical_over_model_point
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (z : T) = 0)
    (c : EtaleChart K T n) (χ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ χ)
    (i₀ : Fin r) (k l : Fin n) (hlk : l ≠ k) (hχ : χ i₀ = some k)
    (hother : ∀ i, i ≠ i₀ → χ i = none)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (ξ i₀) = d)
    (y : T) (hy : y ∈ c.U)
    (hcentered : ∀ a, ¬ IsUnit (T.presheaf.germ c.U y hy (c.coords (MvPolynomial.X a))))
    (e : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk y)) (T.presheaf.stalk y) ≃ₐ[K]
      MvPowerSeries (Fin n) K)
    (he : ∀ a, stalkTaylorExpansion y e (etaleChartStalkCoords c y hy (MvPolynomial.X a)) =
      MvPowerSeries.X a)
    (M : CartierDivisor X) (g : T.functionFieldˣ) (hg : (cartierPullback ρ M).IsLocalEquationAt y g)
    (a : T.presheaf.stalk y) (ha : a ≠ 0)
    (himage : algebraMap (T.presheaf.stalk y) T.functionField a = (g : T.functionField))
    (j : ℕ) (hj : 1 ≤ j)
    (horder : (((n - 1) * d * j : ℕ) : ℕ∞) <
      (powerSeriesDivisorRestriction k (stalkTaylorExpansion y e a)).order) :
    ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) (ρ y) cX f (j * d) (j • D + M) := by
  classical
  let N := (n - 1) * d * j
  let w : Fin n → ℕ := fun i => if i = k then N + 1 else 1
  have hw : w ≠ 0 := by
    intro hz
    have hl := congrFun hz l
    simp only [w, ite_eq_right hlk, Pi.zero_apply] at hl
    exact one_ne_zero hl
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, z, g₀, w', hg₀, hweights,
      hclos, _, hdisc, hdom⟩ := exists_snc_chart_extraction_prime ξ hinj hξ hsnc c χ hc y hy w hw
        (fun i _ => hcentered i)
  let := hUi
  let := hUn
  let := hUo
  let := hUs
  let := hσd
  let := hσo
  obtain ⟨_, hw'⟩ := large_normal_weight_primitive_normalization k l hlk N g₀ hg₀ w' hweights
  let B := crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover
  have hdisc' := hdisc cT (crepantPullbackFormUnit ρ hρ cX f cT) d B hsupp
  rw [crepantBoundaryCartier_smooth_recombine] at hdisc'
  have hsum : ∑ i : Fin n, (w' i : ℤ) = (n + N : ℕ) := by
    rw [hw']
    exact_mod_cast large_normal_weight_sum k N
  have hb : ∑ i, cartierCoefficient B (ξ i) * (((χ i).elim 0 w' : ℕ) : ℤ) =
      (d : ℤ) * (N + 1 : ℕ) := by
    rw [Finset.sum_eq_single i₀]
    · simp only [hχ, Option.elim_some, B, hcrit, hw', ite_true]
    · intro i _ hi
      simp only [hother i hi, Option.elim_none, Nat.cast_zero, mul_zero]
    · intro h
      exact (h (Finset.mem_univ i₀)).elim
  rw [hsum, hb] at hdisc'
  have hwt : ((N + 1 : ℕ) : ℕ∞) ≤ (stalkTaylorExpansion y e a).weightedOrder w' := by
    rw [hw']
    have hr : ((N + 1 : ℕ) : ℕ∞) ≤ (powerSeriesDivisorRestriction k (stalkTaylorExpansion y e a)).order :=
      by simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr horder
    have hh := coordinate_restriction_order_le_large_normal_weightedOrder k (stalkTaylorExpansion y e a) (N + 1) hr
    convert hh using 2
    funext i
    split_ifs <;> rfl
  have hMord := hdom y hy (specializes_refl y) e he a (N + 1) ha hwt
  have hlocal : (cartierPullback ρ M).IsLocalEquationAt (σ (z : U)) g :=
    isLocalEquationAt_of_specializes (specializes_iff_mem_closure.mpr hclos) hg
  have hMcoef : cartierCoefficient (cartierPullback (σ ≫ ρ) M) (z : U) =
      U.ord (dominantFunctionFieldAlgHom (K := K) σ
        (algebraMap (T.presheaf.stalk y) T.functionField a)) (z : U) := by
    rw [cartierPullback_comp,
      cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt σ (cartierPullback ρ M) (z : U) hlocal),
      himage]
    rfl
  intro hlc
  have hσρ := dominantFunctionFieldAlgHom_comp_bijective ρ σ hρ hσ
  have hpoint : ρ y ∈ closure ({((σ ≫ ρ) ≫ 𝟙 X) (z : U)} : Set X) := by
    change ρ y ∈ closure ({ρ (σ (z : U))} : Set X)
    exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hclos).map ρ.continuous)
  have hbound := logPairIsLogCanonicalOverBasePoint_discrepancy_bound_on_birational_test
    (𝟙 X) (ρ y) cX f (j * d) (by nlinarith) (j • D + M) hlc (σ ≫ ρ) hσρ cU z hpoint
  have hnew : logDiscrepancyDivisor n (σ ≫ ρ) hσρ cX f (j * d) (j • D + M) cU etaleCharts_cover =
      j • logDiscrepancyDivisor n (σ ≫ ρ) hσρ cX f d D cU etaleCharts_cover -
        cartierPullback (σ ≫ ρ) M := by
    unfold logDiscrepancyDivisor
    rw [cartierPullback_add, cartierPullback_nsmul]
    module
  rw [hnew, cartierCoefficient_sub, cartierCoefficient_nsmul, hMcoef,
    logDiscrepancyDivisor_comp ρ σ hρ hσ cX f d D cT cU etaleCharts_cover] at hbound
  have hn : 1 ≤ n := by have h := k.isLt; omega
  have hn' : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hN : (N : ℤ) = ((n : ℤ) - 1) * d * j := by
    dsimp [N]
    rw [hn']
  push_cast at hdisc' hMord hbound
  nlinarith

end MixedFujita
