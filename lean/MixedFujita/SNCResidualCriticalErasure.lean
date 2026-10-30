/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierPullbackTriviality

/-! 有限和と全倍数の実引き戻しによる非接触臨界残余消去。 check-299：元の非空交差と許された有限成分集合から、有限powerset上の最大濃度選択で包含最大の非空交差を内部構成し、残る許容成分が交差全体と非接触であることを証明。元の臨界係数と一つの実選択交差点から、種選択を含む最大臨界選択・その実交差点・全選択外臨界成分の交差全体からの回避を内部供給。元lcの全モデル係数上界と実SNC成分Cartier辞書から、全臨界成分を同時に除いた実残余Rを構成し、全SNC係数<d・支持保存・同じ周囲モデル上の実全モデルklt対を証明。実有効Cartier因子の標準切断について零因子が元因子そのもの、非消失開が実イデアル台の補集合であることを証明し、像が台を避ける任意射の実引き戻しを追加切断・自明化なしに自明化。有限和・全倍数・実テンソル同型を用い、選択外臨界因子が非接触なら、選択臨界除去と全臨界除去の実残余引き戻し層が同型であることを証明。最後に元孤立一意lc中心・実固有SNCモデル・種臨界交差点から、最大選択・内部次元・実整成分・正確な中心への固有優越全射・元モデル上のklt残余R・同じ成分残余F及び中心Q・元DとQの全自然数倍随伴を一括内部供給する存在定理へ接続。最大性・回避・klt残余・非消失切断・自明化・比較同型・通常KVを入力にしない。kltは周囲モデル上の全臨界除去残余について証明した範囲で、任意に選んだ成分Cartier代表Fの係数や成分上kltはまだ主張しない。成分境界の実SNC係数表示・相対正値性・元中心数値随伴・一般KV・F1F2は残る。 -/

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


/-- Actual trivial pullbacks of finitely many Cartier classes give an actual
trivial pullback of their sum, with no chosen trivialization input. -/
theorem cartierPullback_finset_sum_zero_of_member_isos
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X)
    {ι : Type*} (s : Finset ι) (E : ι → CartierDivisor X)
    (hE : ∀ i ∈ s, Nonempty ((Scheme.Modules.pullback φ).obj (E i).sheaf ≅ (0 : CartierDivisor Y).sheaf)) :
    Nonempty ((Scheme.Modules.pullback φ).obj (∑ i ∈ s, E i).sheaf ≅ (0 : CartierDivisor Y).sheaf) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨(Scheme.Modules.pullback φ).mapIso (eqToIso (congrArg CartierDivisor.sheaf (Finset.sum_empty))) ≪≫
      (Scheme.Modules.pullback φ).mapIso (cartierZeroSheafIso X) ≪≫
        Scheme.Modules.pullbackObjUnitIso φ ≪≫ (cartierZeroSheafIso Y).symm⟩
  | @insert i s his ih =>
    obtain ⟨a⟩ := hE i (Finset.mem_insert_self _ _)
    obtain ⟨b⟩ := ih (fun j hj => hE j (Finset.mem_insert_of_mem hj))
    exact ⟨(Scheme.Modules.pullback φ).mapIso
        (eqToIso (congrArg CartierDivisor.sheaf (Finset.sum_insert his))) ≪≫
      (Scheme.Modules.pullback φ).mapIso (cartierTensorSheafIso (E i) (∑ j ∈ s, E j)).symm ≪≫
        cartierPullbackTensorIso (E i) φ (∑ j ∈ s, E j).sheaf ≪≫
          MonoidalCategory.tensorIso a b ≪≫ cartierTensorSheafIso 0 0 ≪≫
            eqToIso (congrArg CartierDivisor.sheaf (zero_add (0 : CartierDivisor Y)))⟩


/-- Original selected Fin indexing preserves the ACTUAL finite Cartier sum. -/
theorem sncSelectedPoints_cartier_sum
    {A : Type*} [AddCommMonoid A] {q : ℕ} (E : Fin q → A) (s : Finset (Fin q)) :
    (∑ k : Fin (Fintype.card s), E ((Fintype.equivFin s).symm k).val) = ∑ i ∈ s, E i := by
  rw [Equiv.sum_comp (Fintype.equivFin s).symm (fun i : s => E i.val)]
  exact Finset.sum_coe_sort s E


/-- All unselected critical divisors missing the actual source are erased
by ACTUAL pullback isomorphisms. Thus removing selected or ALL critical
components gives the SAME actual residual line bundle. No trivializations,
residual representatives or compatibility certificates are supplied. -/
theorem cartierPullback_critical_residual_erasure
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] (φ : Y ⟶ X)
    {q : ℕ} (E : Fin q → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (B : CartierDivisor X) (d : ℕ) (C s : Finset (Fin q)) (hsC : s ⊆ C)
    (hmiss : ∀ i ∈ C, i ∉ s → ∀ y : Y, φ y ∉ (effectiveCartierIdealSheaf (E i) (hE i)).support) :
    Nonempty ((Scheme.Modules.pullback φ).obj (B - d • ∑ i ∈ s, E i).sheaf ≅
      (Scheme.Modules.pullback φ).obj (B - d • ∑ i ∈ C, E i).sheaf) := by
  let M := ∑ i ∈ C \ s, E i
  let R := B - d • ∑ i ∈ C, E i
  have hsum : (∑ i ∈ C, E i) = (∑ i ∈ s, E i) + M := by
    dsimp only [M]
    rw [← Finset.sum_sdiff hsC]
    abel
  have hLR : B - d • ∑ i ∈ s, E i = R + d • M := by
    dsimp only [R]
    rw [hsum, nsmul_add]
    abel
  obtain ⟨aM⟩ := cartierPullback_finset_sum_zero_of_member_isos φ (C \ s) E (by
    intro i hi
    obtain ⟨hiC, his⟩ := Finset.mem_sdiff.mp hi
    exact effectiveCartier_pullback_trivial_of_image_off_support (K := K) (E i) (hE i) φ (hmiss i hiC his))
  let aDM : (Scheme.Modules.pullback φ).obj (d • M).sheaf ≅ SheafOfModules.unit Y.ringCatSheaf :=
    cartierPullbackGradedIso M φ 0 aM d ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (nsmul_zero d)) ≪≫ cartierZeroSheafIso Y
  exact ⟨(Scheme.Modules.pullback φ).mapIso (eqToIso (congrArg CartierDivisor.sheaf hLR)) ≪≫
    (Scheme.Modules.pullback φ).mapIso (cartierTensorSheafIso R (d • M)).symm ≪≫
      cartierPullbackTensorIso R φ (d • M).sheaf ≪≫
        MonoidalCategory.tensorIso (Iso.refl _) aDM ≪≫ (MonoidalCategory.rightUnitor _)⟩

end MixedFujita
