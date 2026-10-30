/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCInducedEffectiveMembers

/-! 負係数を保つ実Cartier引き戻し有限和表示。 check-300：実Cartier切断の零イデアルが各茎で切断係数に生成されることと、非零の実引き戻し切断の零イデアルが元零イデアルの実逆像に等しいことを、優越性・平坦性なしに証明。有効Cartier標準切断と生成点での台回避から、正確な逆像イデアル・台・実引き戻し層同型を持つ誘導有効因子を内部構成。有効因子の実イデアルによる一意性を正規性なしで証明し、像全体が台を避ければ誘導因子自体が0と証明。元SNC交差の実整成分の生成点が全選択外成分を避けることを内部供給し、全選択外成分の実誘導有効因子・正確な逆像イデアル・台を構成。実テンソル逆と有限和により負係数を含む符号付き境界の引き戻し表示を構成し、元残余の選択係数0・支持条件から、元係数と実誘導因子の有限和で定まる具体的な成分残余と全自然数倍表示を内部供給。最後に元孤立一意lc中心の299の実最大臨界成分へ適用し、同じ中心射・同じ元Dと中心Qの全倍数随伴をこの具体的残余へ移し、全臨界誘導因子が正確に0であることまで証明。追加の残余代表・非零制限切断・イデアル一致・比較同型を入力にしない。成分上の実SNC素成分分解・係数対応・klt・正値性・数値随伴はまだ証明していない。 -/

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


/-- One actual pullback representation determines every SIGNED integral
multiple, with negative coefficients treated by the actual tensor inverse. -/
theorem cartierPullback_zsmul_representation_of_iso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) (D : CartierDivisor X) (G : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ G.sheaf) (z : ℤ) :
    Nonempty ((Scheme.Modules.pullback φ).obj (z • D).sheaf ≅ (z • G).sheaf) := by
  cases z with
  | ofNat n =>
    change Nonempty ((Scheme.Modules.pullback φ).obj ((n : ℤ) • D).sheaf ≅ ((n : ℤ) • G).sheaf)
    rw [natCast_zsmul, natCast_zsmul]
    exact ⟨cartierPullbackGradedIso D φ G a n⟩
  | negSucc n =>
    exact ⟨by simpa only [negSucc_zsmul] using
      cartierPullbackNegativeIso ( (n + 1) • D) φ ((n + 1) • G) (cartierPullbackGradedIso D φ G a (n + 1))⟩


/-- Actual member pullbacks determine the actual pullback of their finite
SIGNED boundary sum, without positivity assumptions on the coefficients. -/
theorem cartierPullback_finset_signed_sum_of_member_isos
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X)
    {ι : Type*} (s : Finset ι) (E : ι → CartierDivisor X) (G : ι → CartierDivisor Y) (b : ι → ℤ)
    (hA : ∀ i ∈ s, Nonempty ((Scheme.Modules.pullback φ).obj (E i).sheaf ≅ (G i).sheaf)) :
    Nonempty ((Scheme.Modules.pullback φ).obj (∑ i ∈ s, b i • E i).sheaf ≅
      (∑ i ∈ s, b i • G i).sheaf) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨(Scheme.Modules.pullback φ).mapIso (eqToIso (congrArg CartierDivisor.sheaf (Finset.sum_empty))) ≪≫
      (Scheme.Modules.pullback φ).mapIso (cartierZeroSheafIso X) ≪≫
        Scheme.Modules.pullbackObjUnitIso φ ≪≫ (cartierZeroSheafIso Y).symm ≪≫
          eqToIso (congrArg CartierDivisor.sheaf (Finset.sum_empty).symm)⟩
  | @insert i s his ih =>
    obtain ⟨a⟩ := hA i (Finset.mem_insert_self _ _)
    obtain ⟨az⟩ := cartierPullback_zsmul_representation_of_iso φ (E i) (G i) a (b i)
    obtain ⟨asum⟩ := ih (fun k hk => hA k (Finset.mem_insert_of_mem hk))
    exact ⟨(Scheme.Modules.pullback φ).mapIso
      (eqToIso (congrArg CartierDivisor.sheaf (Finset.sum_insert his))) ≪≫
        (Scheme.Modules.pullback φ).mapIso (cartierTensorSheafIso (b i • E i) (∑ k ∈ s, b k • E k)).symm ≪≫
          cartierPullbackTensorIso (b i • E i) φ (∑ k ∈ s, b k • E k).sheaf ≪≫
            MonoidalCategory.tensorIso az asum ≪≫ cartierTensorSheafIso (b i • G i) (∑ k ∈ s, b k • G k) ≪≫
              eqToIso (congrArg CartierDivisor.sheaf (Finset.sum_insert (f := fun k => b k • G k) his).symm)⟩

end MixedFujita
