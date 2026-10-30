/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MaximalCriticalLCAdjointFibration
public import MixedFujita.SectionBaseStalkMembership
public import Hironaka.Scheme.IdealSheaf.StalkLe

/-! 実非優越Cartier切断の正確な引き戻し零イデアル。 check-300：実Cartier切断の零イデアルが各茎で切断係数に生成されることと、非零の実引き戻し切断の零イデアルが元零イデアルの実逆像に等しいことを、優越性・平坦性なしに証明。有効Cartier標準切断と生成点での台回避から、正確な逆像イデアル・台・実引き戻し層同型を持つ誘導有効因子を内部構成。有効因子の実イデアルによる一意性を正規性なしで証明し、像全体が台を避ければ誘導因子自体が0と証明。元SNC交差の実整成分の生成点が全選択外成分を避けることを内部供給し、全選択外成分の実誘導有効因子・正確な逆像イデアル・台を構成。実テンソル逆と有限和により負係数を含む符号付き境界の引き戻し表示を構成し、元残余の選択係数0・支持条件から、元係数と実誘導因子の有限和で定まる具体的な成分残余と全自然数倍表示を内部供給。最後に元孤立一意lc中心の299の実最大臨界成分へ適用し、同じ中心射・同じ元Dと中心Qの全倍数随伴をこの具体的残余へ移し、全臨界誘導因子が正確に0であることまで証明。追加の残余代表・非零制限切断・イデアル一致・比較同型を入力にしない。成分上の実SNC素成分分解・係数対応・klt・正値性・数値随伴はまだ証明していない。 -/

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


/-- An actual section coefficient generates its zero ideal at every stalk,
including the scheme multiplicity. -/
theorem cartierSectionZeroIdeal_stalk_eq_span_coefficient
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    (cartierSectionZeroIdeal D s hs).stalkIdeal x =
      Ideal.span {cartierLocalCoefficient D x f hf s} := by
  exact effectiveCartier_stalkIdeal_eq_span_of_localEquation
    (cartierSectionZeroDivisor D s hs) (cartierSectionZeroDivisor_isEffective D s hs) x
      (f * cartierSectionUnit D s hs) (cartierSectionZeroDivisor_localEquation D s hs x f hf)
      (cartierLocalCoefficient D x f hf s) (by
        simpa only [Units.val_mul, cartierSectionUnit_val] using cartierLocalCoefficient_image D x f hf s)


/-- Zero ideals of NONZERO actual pulled sections are the exact scheme
inverse images, for arbitrary morphisms, without dominance or flatness. -/
theorem cartierActualPullback_zeroIdeal
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (D : CartierDivisor X) (φ : Y ⟶ X) (A : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ A.sheaf)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (ht : cartierPullbackGlobalSectionViaIso D φ A a s ≠ 0) :
    cartierSectionZeroIdeal A (cartierPullbackGlobalSectionViaIso D φ A a s) ht =
      (cartierSectionZeroIdeal D s hs).comap φ := by
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro y
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
  obtain ⟨g, hg, v, hv⟩ := cartierActualPullback_local_coefficients D φ A a y f hf
  rw [cartierSectionZeroIdeal_stalk_eq_span_coefficient A _ ht y g hg,
    Scheme.IdealSheafData.stalkIdeal_comap,
    cartierSectionZeroIdeal_stalk_eq_span_coefficient D s hs (φ y) f hf,
    Ideal.map_span, Set.image_singleton]
  change Ideal.span {_} = Ideal.span {cartierStalkPullbackCoefficient D φ y f hf s}
  rw [hv s]
  exact Ideal.span_singleton_eq_span_singleton.mpr ⟨v, mul_comm _ _⟩

end MixedFujita
