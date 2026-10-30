/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NaturalRestrictionZeroDivisorSupport
public import MixedFujita.AmpleIdealExactBaseLocus
public import MixedFujita.CartierSectionZeroIdeal
public import MixedFujita.FiniteCompleteCartierBaseIdeal

/-! ampleイデアル切断から実有効Cartier閉集合分離。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u v
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- An ample ideal system separates an actual nonempty closed set C
from a closed set Z not contained in C by one ACTUAL nonzero effective
Cartier divisor. No prescribed divisor or section is input. -/
theorem ample_effective_cartier_separates_closed_sets
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (C Z : Closeds X) (hC : (C : Set X).Nonempty) (hnot : ¬ Z ≤ C) :
    ∃ (G : CartierDivisor X) (hG : G.IsEffective), G ≠ 0 ∧
      C ≤ (effectiveCartierIdealSheaf G hG).support ∧
      ¬ Z ≤ (effectiveCartierIdealSheaf G hG).support := by
  classical
  change ¬ ∀ x : X, x ∈ Z → x ∈ C at hnot
  push Not at hnot
  obtain ⟨x, hxZ, hxC⟩ := hnot
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have hIC : I.support = C := SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal C)
  obtain ⟨b₀, hfamily⟩ := ample_ideal_finite_sections_common_zero_locus_exact_support H hH I
  obtain ⟨k, a, _, hunit, hbase⟩ := hfamily (b₀ + 1) (by omega)
  let P := (b₀ + 1) • H
  obtain ⟨i, hi⟩ := hunit x (by simpa only [hIC] using hxC)
  have hai : a i ≠ 0 := (cartierLocalCoefficient_ne_zero_iff P x _ _ _).mp hi.ne_zero
  let G := cartierSectionZeroDivisor P (a i) hai
  have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective P (a i) hai
  have hsup : ((effectiveCartierIdealSheaf G hG).support : Set X) =
      cartierSectionZeroLocus P (a i) := cartierSectionZeroIdeal_support (K := K) P (a i) hai
  have hCG : C ≤ (effectiveCartierIdealSheaf G hG).support := by
    intro y hy
    have hz := (hbase y).mpr (by simpa only [hIC] using hy) i
    change y ∈ ((effectiveCartierIdealSheaf G hG).support : Set X)
    rw [hsup]
    exact hz
  have hZG : ¬ Z ≤ (effectiveCartierIdealSheaf G hG).support := by
    intro hz
    have hxg := hz hxZ
    change x ∈ ((effectiveCartierIdealSheaf G hG).support : Set X) at hxg
    rw [hsup] at hxg
    exact hxg ((mem_cartierSectionNonvanishingOpen_iff_localCoefficient P (a i) x _ _).mpr hi)
  have hnonzero (M : CartierDivisor X) (hM : M.IsEffective)
      (hCM : C ≤ (effectiveCartierIdealSheaf M hM).support) : M ≠ 0 := by
    intro he
    subst M
    obtain ⟨y, hy⟩ := hC
    have hh := hCM hy
    rw [effectiveCartierIdealSheaf_zero_eq_top hM, Scheme.IdealSheafData.support_top] at hh
    exact hh
  exact ⟨G, hG, hnonzero G hG hCG, hCG, hZG⟩

end MixedFujita
