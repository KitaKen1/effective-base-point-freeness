/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.WeightedCriticalSNCNonLC
public import MixedFujita.SNCComponentRestrictionOrder
public import MixedFujita.CenteredEtaleTaylorCoordinates
public import MixedFujita.FiniteTypeClosedPointEvaluation
public import MixedFujita.CartierActualPullbackOrder
public import MixedFujita.CartierBirationalZeroDivisors

/-! 実SNC臨界因子への自然制限高次数から元の非lc点。 See reports/check-264-critical-snc-restriction-nonlc.json for the verified scope. Large normal weights transfer HIGH coordinate-divisor RESTRICTION order to weighted ambient order, allowing low ordinary-order transverse terms. Actual toric extraction cancels the critical normal boundary contribution against the Jacobian. Actual surjective local quotients lift maximal-ideal powers modulo their principal coordinate kernel, avoiding target completion/quotient isomorphisms. On an actual critical SNC component at a closed point away from other components, HIGH NATURAL ORIGINAL SECTION RESTRICTION order internally constructs an ORIGINAL ambient nonLC point with actual centered charts/completion/weighted extraction. Original LC CENTER to critical SNC COMPONENT order transfer and suitable model/point construction remain separate; full original-center concentration/nonLC iteration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- High order on an ACTUAL coefficient-d SNC component at a closed point
away from the other components yields an ORIGINAL ambient non-lc point.
Centered charts, completion coordinates and the actual weighted extraction
are constructed internally. The restriction is to this actual component;
comparison with the original lc-center restriction remains separate. -/
theorem high_order_on_critical_snc_component_not_original_logCanonical
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (z : T) = 0)
    (i₀ : Fin r)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (ξ i₀) = d)
    (J : T.IdealSheafData) (hJ : J = (sncDivisorFamilyOfPoints ξ).component (ULift.up i₀))
    (z : J.subscheme) (hz : IsClosed ({J.subschemeι z} : Set T))
    (hother : ∀ i, i ≠ i₀ → J.subschemeι z ∉ closure ({ξ i} : Set T))
    (M : CartierDivisor X) (g : T.functionFieldˣ)
    (hg : (cartierPullback ρ M).IsLocalEquationAt (J.subschemeι z) g)
    (a : T.presheaf.stalk (J.subschemeι z)) (ha : a ≠ 0)
    (himage : algebraMap (T.presheaf.stalk (J.subschemeι z)) T.functionField a = (g : T.functionField))
    (j : ℕ) (hj : 1 ≤ j)
    (horder : (((n - 1) * d * j : ℕ) : ℕ∞) <
      localAdicOrder (J.subscheme.presheaf.stalk z) ((J.subschemeι.stalkMap z).hom a)) :
    ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) (ρ (J.subschemeι z)) cX f (j * d) (j • D + M) := by
  classical
  let y := J.subschemeι z
  obtain ⟨β⟩ := finiteTypeScheme_closedPoint_has_localEvaluation (K := K) y hz
  obtain ⟨c, χ, hy, hc, hnu, hactive, hpass⟩ := exists_centered_snc_chart ξ hsnc y β
  have hmem : y ∈ (J.support : Set T) := by
    rw [← J.range_subschemeι]
    exact ⟨z, rfl⟩
  have hJsupp := congrArg (fun Q : T.IdealSheafData => (Q.support : Set T)) hJ
  rw [hJsupp] at hmem
  change y ∈ ((Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({ξ i₀} : Set T), isClosed_closure⟩ : Closeds T)).support : Set T) at hmem
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem
  obtain ⟨k, hk⟩ := hpass i₀ hmem
  have hχother (i : Fin r) (hi : i ≠ i₀) : χ i = none := by
    cases hχ : χ i with
    | none => rfl
    | some l => exact (hother i hi (hactive i l hχ)).elim
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨l, hl⟩ := exists_ne k
  obtain ⟨e, he⟩ := centered_etale_chart_exists_unshifted_taylorCoordinates c y hy β hnu
  let N := (n - 1) * d * j
  have hN : ((N + 1 : ℕ) : ℕ∞) ≤
      localAdicOrder (J.subscheme.presheaf.stalk z) ((J.subschemeι.stalkMap z).hom a) := by
    simpa only [Nat.cast_add, Nat.cast_one] using ENat.natCast_add_one_le_iff.mpr horder
  have hformal := snc_component_high_order_formal_coordinate_restriction c ξ χ hc i₀ k hk
    J hJ z hy e (he k) a (N + 1) hN
  have hformal' : (N : ℕ∞) < (powerSeriesDivisorRestriction k (stalkTaylorExpansion y e a)).order := by
    exact ENat.natCast_add_one_le_iff.mp (by simpa only [Nat.cast_add, Nat.cast_one] using hformal)
  exact high_coordinate_restriction_order_not_logCanonical_over_model_point ρ hρ cX f d hd D cT
    ξ hinj hξ hsnc hsupp c χ hc i₀ k l hl hk hχother hcrit y hy hnu e he M g hg a ha himage j hj hformal'


/-- An actual original Cartier section whose NATURAL restriction to an actual
critical SNC component has sufficiently high order gives an ORIGINAL ambient
non-lc point. The local regular equation, its nonzero germ and coordinate/
completion/weighted-extraction comparisons are all internal. -/
theorem high_natural_section_order_on_critical_component_not_original_logCanonical
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (z : T) = 0)
    (i₀ : Fin r)
    (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ cX f d D cT etaleCharts_cover) (ξ i₀) = d)
    (J : T.IdealSheafData) [IsIntegral J.subscheme]
    (hJ : J = (sncDivisorFamilyOfPoints ξ).component (ULift.up i₀))
    (z : J.subscheme) (hz : IsClosed ({J.subschemeι z} : Set T))
    (hother : ∀ i, i ≠ i₀ → J.subschemeι z ∉ closure ({ξ i} : Set T))
    (P : CartierDivisor X) (s : Γ(P.sheaf, ⊤)) (hs : s ≠ 0)
    (Q : CartierDivisor J.subscheme)
    (e : (Scheme.Modules.pullback (J.subschemeι ≫ ρ)).obj P.sheaf ≅ Q.sheaf)
    (j : ℕ) (hj : 1 ≤ j)
    (horder : (((n - 1) * d * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder Q z
      (cartierPullbackGlobalSectionViaIso P (J.subschemeι ≫ ρ) Q e s)) :
    ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) (ρ (J.subschemeι z)) cX f (j * d)
      (j • D + cartierSectionZeroDivisor P s hs) := by
  let y := J.subschemeι z
  obtain ⟨f₀, hf₀⟩ := P.exists_isLocalEquationAt (ρ y)
  let a := cartierStalkPullbackCoefficient P ρ y f₀ hf₀ s
  let g := Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (f₀ * cartierSectionUnit P s hs)
  have hg : (cartierPullback ρ (cartierSectionZeroDivisor P s hs)).IsLocalEquationAt y g :=
    cartierPullback_isLocalEquationAt ρ _ y (cartierSectionZeroDivisor_localEquation P s hs (ρ y) f₀ hf₀)
  have himage : algebraMap (T.presheaf.stalk y) T.functionField a = (g : T.functionField) := by
    dsimp only [a]
    rw [cartierStalkPullbackCoefficient_apply, ← dominantFunctionFieldMap_algebraMap,
      cartierLocalCoefficient_image]
    rfl
  have ha : a ≠ 0 := by
    intro h
    apply Units.ne_zero g
    rw [← himage, h, map_zero]
  have hqa : (J.subschemeι.stalkMap z).hom a =
      cartierStalkPullbackCoefficient P (J.subschemeι ≫ ρ) z f₀ hf₀ s := by
    change (J.subschemeι.stalkMap z).hom ((ρ.stalkMap y).hom
      (cartierLocalCoefficient P (ρ y) f₀ hf₀ s)) =
      ((J.subschemeι ≫ ρ).stalkMap z).hom (cartierLocalCoefficient P (ρ y) f₀ hf₀ s)
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hframe := cartierStalkPullbackOrder_eq_localCoefficient P (J.subschemeι ≫ ρ) z f₀ hf₀ s
  have htarget := cartierStalkPullbackOrder_eq_actualGlobalPullback P (J.subschemeι ≫ ρ) Q e z s
  have hqorder : localAdicOrder (J.subscheme.presheaf.stalk z) ((J.subschemeι.stalkMap z).hom a) =
      cartierSectionVanishingOrder Q z (cartierPullbackGlobalSectionViaIso P (J.subschemeι ≫ ρ) Q e s) :=
    (congrArg (localAdicOrder (J.subscheme.presheaf.stalk z)) hqa).trans (hframe.symm.trans htarget)
  exact high_order_on_critical_snc_component_not_original_logCanonical hn ρ hρ cX f d hd D cT
    ξ hinj hξ hsnc hsupp i₀ hcrit J hJ z hz hother (cartierSectionZeroDivisor P s hs) g hg a ha himage j hj
    (by rwa [hqorder])

end MixedFujita
