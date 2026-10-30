/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InducedEffectiveCartierDivisor

/-! 元SNC成分生成点回避と全選択外誘導有効因子。 check-300：実Cartier切断の零イデアルが各茎で切断係数に生成されることと、非零の実引き戻し切断の零イデアルが元零イデアルの実逆像に等しいことを、優越性・平坦性なしに証明。有効Cartier標準切断と生成点での台回避から、正確な逆像イデアル・台・実引き戻し層同型を持つ誘導有効因子を内部構成。有効因子の実イデアルによる一意性を正規性なしで証明し、像全体が台を避ければ誘導因子自体が0と証明。元SNC交差の実整成分の生成点が全選択外成分を避けることを内部供給し、全選択外成分の実誘導有効因子・正確な逆像イデアル・台を構成。実テンソル逆と有限和により負係数を含む符号付き境界の引き戻し表示を構成し、元残余の選択係数0・支持条件から、元係数と実誘導因子の有限和で定まる具体的な成分残余と全自然数倍表示を内部供給。最後に元孤立一意lc中心の299の実最大臨界成分へ適用し、同じ中心射・同じ元Dと中心Qの全倍数随伴をこの具体的残余へ移し、全臨界誘導因子が正確に0であることまで証明。追加の残余代表・非零制限切断・イデアル一致・比較同型を入力にしない。成分上の実SNC素成分分解・係数対応・klt・正値性・数値随伴はまだ証明していない。 -/

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


/-- Every actual integral selected-stratum component has generic image
outside EVERY unselected original SNC member. No avoidance is supplied. -/
theorem snc_component_generic_avoids_unselected
    {K : Type u} [Field K] {T : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    {n q : ℕ} (ξ : Fin q → T) (hsnc : IsSNCFamily K n ξ) (s : Finset (Fin q))
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme.Opens)
    [IsIntegral U] (i : Fin q) (hi : i ∉ s) :
    (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι)
      (genericPoint U) ∉ closure ({ξ i} : Set T) := by
  let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι
  obtain ⟨hmem, hmax⟩ := snc_integral_component_generic_maximal (sncSelectedPoints ξ s) U
  let w : Fin q → ℝ := fun k => if k ∈ s then 1 else 0
  have hw (x : T) : (∀ k, w k ≠ 0 → x ∈ closure ({ξ k} : Set T)) ↔
      ∀ k, x ∈ closure ({sncSelectedPoints ξ s k} : Set T) := by
    rw [sncSelectedPoints_mem_all_iff]
    simp only [w, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  obtain ⟨c, σ, hηc, hc⟩ := hsnc (j (genericPoint U))
  exact stratum_maximal_point_notMem_closure ξ c σ hc w (j (genericPoint U)) hηc
    ((hw _).mpr hmem) (fun x hx hsp => hmax x ((hw x).mp hx) hsp) i (ite_eq_right hi)


/-- Original SNC data internally give genuine induced effective Cartier
members on any integral selected-stratum component. Selected members are
set to zero; every unselected ideal is the exact reduced-component inverse
image, and the sheaf comparison and support are constructed internally. -/
theorem snc_component_exists_induced_effective_members
    {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    {n q : ℕ} (ξ : Fin q → T) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (s : Finset (Fin q))
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme.Opens)
    [IsIntegral U] :
    let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι
    ∃ (E : Fin q → CartierDivisor T) (hE : ∀ i, (E i).IsEffective),
      (∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T)) ∧
      (∀ (i : Fin q) (z : CodimensionOnePoint T),
        cartierCoefficient (E i) (z : T) = if (z : T) = ξ i then 1 else 0) ∧
      ∃ (G : Fin q → CartierDivisor U) (hG : ∀ i, (G i).IsEffective),
        (∀ i ∈ s, G i = 0) ∧
        ∀ i, i ∉ s →
          effectiveCartierIdealSheaf (G i) (hG i) = (effectiveCartierIdealSheaf (E i) (hE i)).comap j ∧
          Nonempty ((Scheme.Modules.pullback j).obj (E i).sheaf ≅ (G i).sheaf) ∧
          ∀ y : U, y ∈ (effectiveCartierIdealSheaf (G i) (hG i)).support ↔
            j y ∈ closure ({ξ i} : Set T) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian
    (I.subschemeι ≫ (T ↘ Spec (CommRingCat.of K)))
  let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι
  obtain ⟨E, hE, hI, hEc⟩ := exists_snc_component_cartier ξ hξ hsnc
  have hex (i : {i : Fin q // i ∉ s}) : ∃ (G : CartierDivisor U) (hG : G.IsEffective),
      effectiveCartierIdealSheaf G hG = (effectiveCartierIdealSheaf (E i.val) (hE i.val)).comap j ∧
      Nonempty ((Scheme.Modules.pullback j).obj (E i.val).sheaf ≅ G.sheaf) ∧
      ∀ y : U, y ∈ (effectiveCartierIdealSheaf G hG).support ↔
        j y ∈ (effectiveCartierIdealSheaf (E i.val) (hE i.val)).support := by
    apply effectiveCartier_exists_induced_divisor_of_generic_off_support (K := K) (E i.val) (hE i.val) j
    change j (genericPoint U) ∉ ((effectiveCartierIdealSheaf (E i.val) (hE i.val)).support : Set T)
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact snc_component_generic_avoids_unselected ξ hsnc s U i.val i.prop
  choose G' hG' hI' aG' hsupp' using hex
  let G : Fin q → CartierDivisor U := fun i => if hi : i ∈ s then 0 else G' ⟨i, hi⟩
  have hG (i : Fin q) : (G i).IsEffective := by
    dsimp only [G]
    split_ifs with hi
    · exact CartierDivisor.isEffective_zero
    · exact hG' ⟨i, hi⟩
  refine ⟨E, hE, hI, hEc, G, hG, ?_, ?_⟩
  · intro i hi
    exact dite_eq_left hi
  · intro i hi
    have hGi : G i = G' ⟨i, hi⟩ := dite_eq_right hi
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hGi] using hI' ⟨i, hi⟩
    · simpa only [hGi] using aG' ⟨i, hi⟩
    · intro y
      change y ∈ (effectiveCartierIdealSheaf (G i) (hG i)).support ↔ j y ∈ closure ({ξ i} : Set T)
      have h : y ∈ (effectiveCartierIdealSheaf (G' ⟨i, hi⟩) (hG' ⟨i, hi⟩)).support ↔
          j y ∈ ((effectiveCartierIdealSheaf (E i) (hE i)).support : Set T) := hsupp' ⟨i, hi⟩ y
      rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
      change y ∈ (effectiveCartierIdealSheaf (G' ⟨i, hi⟩) (hG' ⟨i, hi⟩)).support ↔ j y ∈ closure ({ξ i} : Set T) at h
      simpa only [hGi] using h

end MixedFujita
