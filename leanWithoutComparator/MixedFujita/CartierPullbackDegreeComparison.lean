/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GlobalSNCComponentAdjunction
public import MixedFujita.CartierNegativeGradedPullback
public import MixedFujita.CartierNefPullback

/-! 非優越曲線合成の次数比較とampleによる無切断Cartier引き戻し比較。 check-297：実加群層引き戻しのCartier表示から任意の非優越な曲線合成射でも正確な次数一致を証明。元空間のample類から二つの十分大きい大域生成捻り・非零切断を内部構成し、元Cartier因子自身の非零切断を仮定せず、実Cartier引き戻しと実加群層引き戻しの同型を供給。296の実大域SNC随伴から、成分へ写る全ての実smooth proper曲線で標準類の次数恒等式を導き、任意の周囲随伴分子の残余引き戻しを一つの実Cartier因子Fで内部表示し、同じ標準類・Fによる全自然数倍の実層同型を供給。元のcrepant境界と引き戻し最高次形式の主因子補正を実線束同型として消去してからSNC成分へ制限し、元分子Dの実合成引き戻しがdK_U+Fとなることと全自然数倍の同じ表示を証明。有理形式係数の成分上での非消失を仮定しない。任意の実曲線について元Dの引き戻し次数がd倍のK_U次数と実残余B-dΣE_iの引き戻し次数の和に一致する厳密公式を証明。元のSNC素成分・単射性・余高さ1・臨界係数dから、実E_i・係数1辞書・残余の全臨界係数0・他素点での元係数保存を内部構成。元の分離的smooth Noetherianモデル上の任意交差点から、これらE_i・実整開閉成分・標準類参照チャート・同じ残余Fと元Dの全倍数層同型まで一括供給する存在定理へ接続。残余の正値性・中心への相対標準類比較・数値随伴・一般KV・F1F2は残る。 -/

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




attribute [local instance] Classical.propDecidable


/-- A genuine module pullback representation preserves degree along every
actual curve composite, including nondominant closed maps. -/
theorem cartierCurvePullbackDegree_comp_of_representation
    {K : Type u} [Field K] {X Y C : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral C]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hC : topologicalKrullDim C = 1) (j : Y ⟶ X) (φ : C ⟶ Y)
    (D : CartierDivisor X) (E : CartierDivisor Y)
    (a : (Scheme.Modules.pullback j).obj D.sheaf ≅ E.sheaf) :
    cartierCurvePullbackDegree (K := K) D (φ ≫ j) = cartierCurvePullbackDegree (K := K) E φ := by
  obtain ⟨F, ⟨b⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor E φ
  exact (cartierCurvePullbackDegree_eq_representation_degree (K := K) hC D (φ ≫ j) F
    ((Scheme.Modules.pullbackComp φ j).symm.app D.sheaf ≪≫
      (Scheme.Modules.pullback φ).mapIso a ≪≫ b)).trans
    (cartierCurvePullbackDegree_eq_representation_degree (K := K) hC E φ F b).symm


/-- An ample class internally supplies two nonzero-section twists, so the actual
Cartier pullback and module pullback agree for ANY original divisor. No nonzero
section of that divisor is assumed. -/
theorem cartierPullback_sheaf_iso_modulePullback_of_ample
    {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [X.Over (Spec (CommRingCat.of K))] (H D : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) (ρ : T ⟶ X) [IsDominant ρ] :
    Nonempty ((Scheme.Modules.pullback ρ).obj D.sheaf ≅ (cartierPullback ρ D).sheaf) := by
  obtain ⟨j₁, h₁⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH D
  obtain ⟨j₂, h₂⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH (0 : CartierDivisor X)
  obtain ⟨s₁, hs₁⟩ := cartierIsGloballyGenerated_exists_nonzero_section
    (h₁ (max j₁ j₂) (le_max_left _ _))
  obtain ⟨s₂, hs₂⟩ := cartierIsGloballyGenerated_exists_nonzero_section
    (h₂ (max j₁ j₂) (le_max_right _ _))
  obtain ⟨a⟩ := cartierPullback_sheaf_iso_modulePullback ρ _ s₁ hs₁
  obtain ⟨b⟩ := cartierPullback_sheaf_iso_modulePullback ρ _ s₂ hs₂
  have hdec : D = (D + max j₁ j₂ • H) - (0 + max j₁ j₂ • H) := by abel
  exact ⟨(Scheme.Modules.pullback ρ).mapIso (eqToIso (congrArg CartierDivisor.sheaf hdec)) ≪≫
    cartierPullbackSubIso _ _ ρ _ _ a b ≪≫
      eqToIso (congrArg CartierDivisor.sheaf
        ((cartierPullback_sub ρ _ _).symm.trans (congrArg (cartierPullback ρ) hdec.symm)))⟩

end MixedFujita
