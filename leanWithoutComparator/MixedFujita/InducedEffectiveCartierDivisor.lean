/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPullbackZeroIdeals

/-! 実逆像イデアルによる誘導有効Cartier因子の存在一意性と実消去。 check-300：実Cartier切断の零イデアルが各茎で切断係数に生成されることと、非零の実引き戻し切断の零イデアルが元零イデアルの実逆像に等しいことを、優越性・平坦性なしに証明。有効Cartier標準切断と生成点での台回避から、正確な逆像イデアル・台・実引き戻し層同型を持つ誘導有効因子を内部構成。有効因子の実イデアルによる一意性を正規性なしで証明し、像全体が台を避ければ誘導因子自体が0と証明。元SNC交差の実整成分の生成点が全選択外成分を避けることを内部供給し、全選択外成分の実誘導有効因子・正確な逆像イデアル・台を構成。実テンソル逆と有限和により負係数を含む符号付き境界の引き戻し表示を構成し、元残余の選択係数0・支持条件から、元係数と実誘導因子の有限和で定まる具体的な成分残余と全自然数倍表示を内部供給。最後に元孤立一意lc中心の299の実最大臨界成分へ適用し、同じ中心射・同じ元Dと中心Qの全倍数随伴をこの具体的残余へ移し、全臨界誘導因子が正確に0であることまで証明。追加の残余代表・非零制限切断・イデアル一致・比較同型を入力にしない。成分上の実SNC素成分分解・係数対応・klt・正値性・数値随伴はまだ証明していない。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
attribute [local instance] Classical.propDecidable


/-- A canonical effective divisor is induced by every actual morphism whose
generic point avoids the original support; its exact ideal and module class
are constructed internally. -/
theorem effectiveCartier_exists_induced_divisor_of_generic_off_support
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [X.Over (Spec (CommRingCat.of K))] (E : CartierDivisor X) (hE : E.IsEffective)
    (φ : Y ⟶ X) (hη : φ (genericPoint Y) ∉ (effectiveCartierIdealSheaf E hE).support) :
    ∃ (G : CartierDivisor Y) (hG : G.IsEffective),
      effectiveCartierIdealSheaf G hG = (effectiveCartierIdealSheaf E hE).comap φ ∧
      Nonempty ((Scheme.Modules.pullback φ).obj E.sheaf ≅ G.sheaf) ∧
      ∀ y : Y, y ∈ (effectiveCartierIdealSheaf G hG).support ↔
        φ y ∈ (effectiveCartierIdealSheaf E hE).support := by
  obtain ⟨s, hs, hz, hsupp⟩ := effectiveCartier_exists_canonical_section_with_exact_nonvanishing (K := K) E hE
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor E φ
  let t := cartierPullbackGlobalSectionViaIso E φ A a s
  have ht : t ≠ 0 := by
    apply (cartierSectionNonvanishingOpen_nonempty_iff A t).mp
    refine ⟨genericPoint Y, ?_⟩
    rw [cartierActualPullback_nonvanishingOpen]
    exact (hsupp _).mpr hη
  let G := cartierSectionZeroDivisor A t ht
  have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective A t ht
  have hI : effectiveCartierIdealSheaf G hG = (effectiveCartierIdealSheaf E hE).comap φ := by
    have h := cartierActualPullback_zeroIdeal E φ A a s hs ht
    change effectiveCartierIdealSheaf G hG =
      (effectiveCartierIdealSheaf (cartierSectionZeroDivisor E s hs) _).comap φ at h
    simpa only [hz] using h
  refine ⟨G, hG, hI, ⟨a ≪≫ (cartierSheafPrincipalShiftIso A (cartierSectionUnit A t ht)).symm⟩, ?_⟩
  intro y
  rw [hI, Scheme.IdealSheafData.support_comap]
  rfl


/-- Effective Cartier divisors are determined by their ACTUAL ideal sheaves,
without normality of the integral scheme. -/
theorem effectiveCartier_eq_of_idealSheaf_eq
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (D E : CartierDivisor X) (hD : D.IsEffective) (hE : E.IsEffective)
    (hI : effectiveCartierIdealSheaf D hD = effectiveCartierIdealSheaf E hE) : D = E := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro x
  obtain ⟨U, hxU, hneU, a, ha, hEqD⟩ := exists_affineOpen_regularEquation_of_isEffective D hD x
  obtain ⟨V, hxV, hneV, b, hb, hEqE⟩ := exists_affineOpen_regularEquation_of_isEffective E hE x
  let : Nonempty U.1 := hneU
  let : Nonempty V.1 := hneV
  let f := regularEquationRationalUnit X U.1 a ha
  let g := regularEquationRationalUnit X V.1 b hb
  have hf : D.IsLocalEquationAt x f := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEqD hxU
  have hg : E.IsLocalEquationAt x g := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEqE hxV
  let ax := X.presheaf.germ U.1 x hxU a
  let bx := X.presheaf.germ V.1 x hxV b
  have hax : algebraMap (X.presheaf.stalk x) X.functionField ax = (f : X.functionField) := by
    exact (X.algebraMap_germ_eq_germToFunctionField hxU a).trans (regularEquationRationalUnit_val X U.1 a ha).symm
  have hbx : algebraMap (X.presheaf.stalk x) X.functionField bx = (g : X.functionField) := by
    exact (X.algebraMap_germ_eq_germToFunctionField hxV b).trans (regularEquationRationalUnit_val X V.1 b hb).symm
  have hspan : Ideal.span {ax} = Ideal.span {bx} := by
    rw [← effectiveCartier_stalkIdeal_eq_span_of_localEquation D hD x f hf ax hax,
      ← effectiveCartier_stalkIdeal_eq_span_of_localEquation E hE x g hg bx hbx, hI]
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨f, hf, isLocalEquationAt_of_eq_unit_mul hg w ?_⟩
  rw [← hbx, ← hw, map_mul, hax, mul_comm]


/-- The induced effective divisor is UNIQUE as an actual Cartier divisor,
not merely unique up to principal translation. -/
theorem effectiveCartier_existsUnique_induced_divisor
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [X.Over (Spec (CommRingCat.of K))] (E : CartierDivisor X) (hE : E.IsEffective)
    (φ : Y ⟶ X) (hη : φ (genericPoint Y) ∉ (effectiveCartierIdealSheaf E hE).support) :
    ∃! G : CartierDivisor Y, ∃ hG : G.IsEffective,
      effectiveCartierIdealSheaf G hG = (effectiveCartierIdealSheaf E hE).comap φ ∧
      Nonempty ((Scheme.Modules.pullback φ).obj E.sheaf ≅ G.sheaf) := by
  obtain ⟨G, hG, hI, a, _hsupp⟩ := effectiveCartier_exists_induced_divisor_of_generic_off_support (K := K) E hE φ hη
  refine ⟨G, ⟨hG, hI, a⟩, ?_⟩
  rintro G' ⟨hG', hI', _a'⟩
  exact effectiveCartier_eq_of_idealSheaf_eq G' G hG' hG (hI'.trans hI.symm)


/-- If the whole image avoids the divisor, its induced divisor is EXACTLY
zero, rather than just principal or linearly trivial. -/
theorem effectiveCartier_induced_divisor_eq_zero_of_image_off_support
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (E : CartierDivisor X) (hE : E.IsEffective) (φ : Y ⟶ X)
    (G : CartierDivisor Y) (hG : G.IsEffective)
    (hI : effectiveCartierIdealSheaf G hG = (effectiveCartierIdealSheaf E hE).comap φ)
    (hmiss : ∀ y : Y, φ y ∉ (effectiveCartierIdealSheaf E hE).support) : G = 0 := by
  apply effectiveCartier_eq_of_idealSheaf_eq G 0 hG CartierDivisor.isEffective_zero
  rw [effectiveCartierIdealSheaf_zero_eq_top]
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro y
  rw [Scheme.IdealSheafData.stalkIdeal_top]
  apply Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support
  rw [hI, Scheme.IdealSheafData.support_comap]
  exact hmiss y

end MixedFujita
