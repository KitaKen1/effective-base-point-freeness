/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MaximalCriticalSNCSelection
public import MixedFujita.SNCBoundaryKlt

/-! 元lcから周囲全臨界除去残余の実全モデルklt。 check-299：元の非空交差と許された有限成分集合から、有限powerset上の最大濃度選択で包含最大の非空交差を内部構成し、残る許容成分が交差全体と非接触であることを証明。元の臨界係数と一つの実選択交差点から、種選択を含む最大臨界選択・その実交差点・全選択外臨界成分の交差全体からの回避を内部供給。元lcの全モデル係数上界と実SNC成分Cartier辞書から、全臨界成分を同時に除いた実残余Rを構成し、全SNC係数<d・支持保存・同じ周囲モデル上の実全モデルklt対を証明。実有効Cartier因子の標準切断について零因子が元因子そのもの、非消失開が実イデアル台の補集合であることを証明し、像が台を避ける任意射の実引き戻しを追加切断・自明化なしに自明化。有限和・全倍数・実テンソル同型を用い、選択外臨界因子が非接触なら、選択臨界除去と全臨界除去の実残余引き戻し層が同型であることを証明。最後に元孤立一意lc中心・実固有SNCモデル・種臨界交差点から、最大選択・内部次元・実整成分・正確な中心への固有優越全射・元モデル上のklt残余R・同じ成分残余F及び中心Q・元DとQの全自然数倍随伴を一括内部供給する存在定理へ接続。最大性・回避・klt残余・非消失切断・自明化・比較同型・通常KVを入力にしない。kltは周囲モデル上の全臨界除去残余について証明した範囲で、任意に選んだ成分Cartier代表Fの係数や成分上kltはまだ主張しない。成分境界の実SNC係数表示・相対正値性・元中心数値随伴・一般KV・F1F2は残る。 -/

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


/-- Remove ALL actual critical SNC components globally. Original lc bounds
and genuine coefficient-one Cartier components give a signed residual with
coefficients<d and an ACTUAL all-model klt pair on the same ambient model.
No residual, coefficient dictionary or klt certificate is supplied. -/
theorem original_lc_snc_exists_all_critical_removed_klt_residual
    {K : Type u} [Field K] [CharZero K] {n q : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (cT : EtaleChart K T n)
    (ξ : Fin q → T) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (z : T) = 0) :
    let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
    let C := Finset.univ.filter fun i => cartierCoefficient B (ξ i) = (d : ℤ)
    ∃ (E : Fin q → CartierDivisor T) (hE : ∀ i, (E i).IsEffective)
      (_hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T)),
      (∀ (i : Fin q) (z : CodimensionOnePoint T),
        cartierCoefficient (E i) (z : T) = if (z : T) = ξ i then 1 else 0) ∧
      let R := B - d • ∑ i ∈ C, E i
      (∀ i, cartierCoefficient R (ξ i) < (d : ℤ)) ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient R (z : T) = 0) ∧
      LogPairIsKlt cT 1 d (d • smoothCanonicalDivisor cT + R) := by
  classical
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let C := Finset.univ.filter fun i => cartierCoefficient B (ξ i) = (d : ℤ)
  obtain ⟨E, hE, hI, hEc⟩ := exists_snc_component_cartier ξ hξ hsnc
  let R := B - d • ∑ i ∈ C, E i
  have hsum (k : Fin q) : cartierCoefficient (∑ i ∈ C, E i) (ξ k) = if k ∈ C then 1 else 0 := by
    rw [cartierCoefficient_sum]
    simp only [hEc _ ⟨ξ k, hξ k⟩]
    simp only [hinj.eq_iff, Finset.sum_ite_eq]
  have hstrict (k : Fin q) : cartierCoefficient R (ξ k) < (d : ℤ) := by
    dsimp only [R]
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, hsum]
    by_cases hk : k ∈ C
    · rw [ite_eq_left hk, (Finset.mem_filter.mp hk).2, mul_one, sub_self]
      exact_mod_cast (show 0 < d by omega)
    · rw [ite_eq_right hk, mul_zero, sub_zero]
      have hle := logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hlc cT ⟨ξ k, hξ k⟩
      have hne : cartierCoefficient B (ξ k) ≠ (d : ℤ) := by
        simpa only [C, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      exact lt_of_le_of_ne hle hne
  have hRsupp (z : CodimensionOnePoint T) (hz : (z : T) ∉ Set.range ξ) :
      cartierCoefficient R (z : T) = 0 := by
    dsimp only [R]
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, hsupp z hz, cartierCoefficient_sum]
    have hzero (i : Fin q) : cartierCoefficient (E i) (z : T) = 0 := by
      rw [hEc i z, ite_eq_right (fun h => hz ⟨i, h.symm⟩)]
    simp only [hzero, Finset.sum_const_zero, mul_zero, sub_zero]
  refine ⟨E, hE, hI, hEc, hstrict, hRsupp, ?_⟩
  simpa only [principalCartierDivisor_one, add_zero] using
    isSNCFamily_logPairIsKlt cT 1 d hd R ξ hinj hξ hsnc hRsupp hstrict

end MixedFujita
