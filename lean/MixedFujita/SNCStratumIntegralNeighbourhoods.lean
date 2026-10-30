/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCStratumPointCharts
public import MixedFujita.ProperIntegralSmoothComponent

/-! 元SNC幾何から実最終整成分と整切断近傍を内部構成。 check-292：実SNC閉層の各点が元の全成分閉包に属することを実イデアル台の反変性から証明し、元IsSNCFamilyだけから全選択成分に座標の付くチャートと、非整・非連結にも対応する実閉層全体の残余エタール被覆を内部構成。任意affine細分でも元SNC条件が保たれることを証明し、元有効Cartier因子の実局所方程式を任意の指定近傍内の同じSNCチャートに内部供給。元滑らかなNoetherian SNCモデルから、既存正則成分APIで各点を通る実開閉整成分、その周囲開持ち上げ、元空間への実閉埋込みを構成し、その成分内の実整切断近傍と元Cartier方程式を同時供給。元幾何だけを持つSNCAdjunctionChartと、291の内部残余座標を使う実切断チャートを定義し、これらが実閉層全体を覆うことを証明。成分上への標準層同型の移送・重なり一致・大域SNC随伴と数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Original smooth Noetherian SNC geometry supplies an ACTUAL final clopen
INTEGRAL component through every stratum point, an ambient open lifting it,
and the original closed immersion of that component. No component certificate. -/
theorem snc_stratum_exists_lifted_integral_component
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]
    {n m : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K n ξ)
    (y : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    ∃ (U : I.subscheme.Opens) (W : X.Opens), y ∈ U ∧ I.subschemeι y ∈ W ∧
      I.subschemeι ⁻¹ᵁ W = U ∧ IsClosed (U : Set I.subscheme) ∧ IsIntegral U ∧
        IsClosedImmersion (U.ι ≫ I.subschemeι) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : NoetherianSpace I.subscheme := I.subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : IsNoetherian I.subscheme := {}
  let : IsRegular I.subscheme := sncStratum_isRegular K (sncDivisorFamilyOfPoints ξ)
    (sncDivisorFamilyOfPoints_isSnc ξ hsnc) Finset.univ
  obtain ⟨U, hy, hclosed, hint, hι⟩ := regularScheme_exists_clopen_integral_component y
  obtain ⟨W, _hW, hWU⟩ := inducing_relative_open_lift I.subschemeι.isClosedEmbedding.isInducing
    (⊤ : X.Opens) U (by intro z hz; trivial)
  let := hι
  refine ⟨U, W, hy, ?_, hWU, hclosed, hint, inferInstance⟩
  change y ∈ I.subschemeι ⁻¹ᵁ W
  rwa [hWU]


/-- Original SNC geometry and genuine Cartier equations jointly supply an
INTEGRAL actual cut neighbourhood inside a constructed final integral component.
Neither whole-stratum nor intermediate-stratum integrality is assumed. -/
theorem snc_stratum_exists_integral_equation_neighbourhood
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]
    {n m : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K n ξ)
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (y : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    ∃ (U : I.subscheme.Opens) (c : EtaleChart K X n) (τ : Fin m → Fin n)
      (g : Fin m → Γ(X, c.U)) (hg : ∀ i, g i ≠ 0),
      y ∈ I.subschemeι ⁻¹ᵁ c.U ∧ I.subschemeι ⁻¹ᵁ c.U ≤ U ∧ IsClosed (U : Set I.subscheme) ∧
      IsIntegral U ∧ IsIntegral (I.subschemeι ⁻¹ᵁ c.U) ∧ IsClosedImmersion (U.ι ≫ I.subschemeι) ∧
      IsSNCChart c ξ (fun i => some (τ i)) ∧
      ∀ i, rationalUnitClass X c.U (Additive.ofMul (regularEquationRationalUnit X c.U (g i) (hg i))) =
        E i |_ c.U := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  obtain ⟨U, O, _hyU, hyO, hOU, hclosed, hint, hι⟩ := snc_stratum_exists_lifted_integral_component ξ hsnc y
  obtain ⟨c, τ, g, hg, hp, hcO, hc, hEq⟩ := snc_stratum_exists_cartier_equation_chart_at ξ hsnc E hE y O hyO
  have hcut : I.subschemeι ⁻¹ᵁ c.U ≤ U := by
    rw [← hOU]
    exact fun _z hz => hcO hz
  let : IsIntegral U := hint
  let : Nonempty (I.subschemeι ⁻¹ᵁ c.U) := ⟨⟨y, hp⟩⟩
  have hintcut : IsIntegral (I.subschemeι ⁻¹ᵁ c.U) :=
    isIntegral_of_isOpenImmersion (I.subscheme.homOfLE hcut)
  exact ⟨U, c, τ, g, hg, hp, hcut, hclosed, hint, hintcut, hι, hc, hEq⟩

end MixedFujita
