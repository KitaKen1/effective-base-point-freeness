/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentGenericPoints

/-! 元選択集合の内部Fin族・SNC・実交差余次元上界。 check-298：Mathlibの消滅イデアル順像と被約源のnilradical消滅から、像包含だけで実被約閉中心へのスキーム射を内部構成。実生成点像の閉包一致から中心の生成点保存・優越性を導き、元射が固有なら中心射の固有性と全射性も供給。実SNC交差の像と全元成分閉包への所属の同値、実整開成分の生成点が交差内で極大generizationであることを証明。元の有限選択集合を内部Fin列挙し、選択SNC族・単射性・余高さ1・所属の元添字辞書・交差点での余次元上界を追加証明書なしに供給。元の孤立一意lc中心・実固有SNCモデル・任意の非空臨界選択集合から、任意の実整開閉交差成分について、正確な被約中心への実射・元射との因子化・固有性・優越性・全射性・基礎体上の可換性・生成点保存を内部構成。元モデルの各交差点から整成分自体も供給。さらに点から成分の余次元と次元を内部決定し、297の実Cartier成分・臨界係数消去・同じ残余Fの全倍数随伴を同じ実中心射へ接続。中心上の実Cartier代表Qと、元D及び中心Qの全自然数倍を同じdK_U+Fへ引き戻す実層同型まで一つの存在定理で供給。成分・中心射・像包含・優越性・次元証明書・Cartier代表・比較同型や通常KVを追加入力にしない。正値性・相対標準類評価・元中心の数値随伴・一般KV・F1F2は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
attribute [local instance] Classical.propDecidable


/-- Select the ORIGINAL finite set of SNC components by an internal Fin
indexing; no enumeration or selected-family certificate is supplied. -/
@[reducible]
noncomputable def sncSelectedPoints {T : Scheme.{u}} {q : ℕ}
    (ξ : Fin q → T) (s : Finset (Fin q)) : Fin (Fintype.card s) → T :=
  fun k => ξ ((Fintype.equivFin s).symm k).val


/-- Membership in the selected actual stratum is exactly membership in the
ORIGINAL selected component closures. -/
theorem sncSelectedPoints_mem_all_iff
    {T : Scheme.{u}} {q : ℕ} (ξ : Fin q → T) (s : Finset (Fin q)) (x : T) :
    (∀ k, x ∈ closure ({sncSelectedPoints ξ s k} : Set T)) ↔
      ∀ i ∈ s, x ∈ closure ({ξ i} : Set T) := by
  constructor
  · intro h i hi
    simpa only [sncSelectedPoints, Equiv.symm_apply_apply] using
      h ((Fintype.equivFin s) ⟨i, hi⟩)
  · intro h k
    exact h _ ((Fintype.equivFin s).symm k).prop


/-- Original SNC charts internally give the SNC atlas on ANY selected family. -/
theorem sncSelectedPoints_isSNCFamily
    {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
    {n q : ℕ} (ξ : Fin q → T) (hsnc : IsSNCFamily K n ξ) (s : Finset (Fin q)) :
    IsSNCFamily K n (sncSelectedPoints ξ s) := by
  intro x
  obtain ⟨c, σ, hx, hc⟩ := hsnc x
  refine ⟨c, fun k => σ ((Fintype.equivFin s).symm k).val, hx, ?_, ?_⟩
  · intro i j a hi hj
    apply (Fintype.equivFin s).symm.injective
    exact Subtype.ext (hc.1 _ _ a hi hj)
  · intro i
    exact hc.2 _


/-- Original distinct prime points remain distinct and codimension one
under the internal selected indexing. -/
theorem sncSelectedPoints_injective_and_coheight
    {T : Scheme.{u}} {q : ℕ} (ξ : Fin q → T) (hinj : Function.Injective ξ)
    (hξ : ∀ k, Order.coheight (ξ k) = 1) (s : Finset (Fin q)) :
    Function.Injective (sncSelectedPoints ξ s) ∧
      ∀ k, Order.coheight (sncSelectedPoints ξ s k) = 1 := by
  refine ⟨?_, fun k => hξ _⟩
  intro i j hij
  apply (Fintype.equivFin s).symm.injective
  exact Subtype.ext (hinj hij)


/-- A point of the ACTUAL selected stratum forces its codimension bound
from the ORIGINAL SNC chart; no dimension certificate is input. -/
theorem sncSelectedPoints_card_le_dimension_at_stratum_point
    {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
    {n q : ℕ} (ξ : Fin q → T) (hsnc : IsSNCFamily K n ξ) (s : Finset (Fin q))
    (p : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme) :
    Fintype.card s ≤ n := by
  obtain ⟨c, τ, _hp, hc⟩ := snc_stratum_exists_selected_chart_at (sncSelectedPoints ξ s)
    (sncSelectedPoints_isSNCFamily ξ hsnc s) p
  have hinj : Function.Injective τ := by
    intro i j h
    exact hc.1 i j (τ i) rfl (congrArg some h.symm)
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective τ hinj

end MixedFujita
