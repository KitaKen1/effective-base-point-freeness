/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SignedCartierPullbackSums

/-! 元支持と係数からの具体的誘導成分残余と全倍数表示。 check-300：実Cartier切断の零イデアルが各茎で切断係数に生成されることと、非零の実引き戻し切断の零イデアルが元零イデアルの実逆像に等しいことを、優越性・平坦性なしに証明。有効Cartier標準切断と生成点での台回避から、正確な逆像イデアル・台・実引き戻し層同型を持つ誘導有効因子を内部構成。有効因子の実イデアルによる一意性を正規性なしで証明し、像全体が台を避ければ誘導因子自体が0と証明。元SNC交差の実整成分の生成点が全選択外成分を避けることを内部供給し、全選択外成分の実誘導有効因子・正確な逆像イデアル・台を構成。実テンソル逆と有限和により負係数を含む符号付き境界の引き戻し表示を構成し、元残余の選択係数0・支持条件から、元係数と実誘導因子の有限和で定まる具体的な成分残余と全自然数倍表示を内部供給。最後に元孤立一意lc中心の299の実最大臨界成分へ適用し、同じ中心射・同じ元Dと中心Qの全倍数随伴をこの具体的残余へ移し、全臨界誘導因子が正確に0であることまで証明。追加の残余代表・非零制限切断・イデアル一致・比較同型を入力にしない。成分上の実SNC素成分分解・係数対応・klt・正値性・数値随伴はまだ証明していない。 -/

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


/-- Vanishing selected coefficients remove those normal components BEFORE
restriction. The actual residual pullback is the signed sum of the genuine
induced divisors, using normality solely to recover the original divisor. -/
theorem supported_cartier_induced_signed_sum_representation
    {T Y : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsIntegral Y]
    (hnorm : ∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x))
    (j : Y ⟶ T) {q : ℕ} (ξ : Fin q → T) (hinj : Function.Injective ξ)
    (E : Fin q → CartierDivisor T)
    (hEc : ∀ (i : Fin q) (z : CodimensionOnePoint T),
      cartierCoefficient (E i) (z : T) = if (z : T) = ξ i then 1 else 0)
    (R : CartierDivisor T)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient R (z : T) = 0)
    (s : Finset (Fin q)) (hzero : ∀ i ∈ s, cartierCoefficient R (ξ i) = 0)
    (G : Fin q → CartierDivisor Y)
    (hA : ∀ i, i ∉ s → Nonempty ((Scheme.Modules.pullback j).obj (E i).sheaf ≅ (G i).sheaf)) :
    Nonempty ((Scheme.Modules.pullback j).obj R.sheaf ≅
      (∑ i ∈ sᶜ, cartierCoefficient R (ξ i) • G i).sheaf) := by
  have hsum : R = ∑ i ∈ sᶜ, cartierCoefficient R (ξ i) • E i := by
    calc
      R = ∑ i, cartierCoefficient R (ξ i) • E i :=
        cartierDivisor_eq_member_combination hnorm ξ hinj E hEc R hsupp
      _ = ∑ i ∈ sᶜ, cartierCoefficient R (ξ i) • E i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _hi hi
        have his : i ∈ s := by simpa only [Finset.mem_compl, not_not] using hi
        rw [hzero i his, zero_smul]
  obtain ⟨a⟩ := cartierPullback_finset_signed_sum_of_member_isos j sᶜ E G
    (fun i => cartierCoefficient R (ξ i)) (fun i hi => hA i (Finset.mem_compl.mp hi))
  exact ⟨(Scheme.Modules.pullback j).mapIso (eqToIso (congrArg CartierDivisor.sheaf hsum)) ≪≫ a⟩


/-- The ORIGINAL smooth SNC geometry and a residual vanishing on selected
normals internally construct a SPECIFIC signed induced boundary and its
actual representation in ALL natural multiples. No representative, inverse
image ideal, nonzero restricted section or class comparison is input. -/
theorem snc_component_exists_induced_signed_residual
    {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [T.Over (Spec (CommRingCat.of K))] [Smooth (T ↘ Spec (CommRingCat.of K))]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    {n q : ℕ} (ξ : Fin q → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (s : Finset (Fin q))
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme.Opens)
    [IsIntegral U] (R : CartierDivisor T)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient R (z : T) = 0)
    (hzero : ∀ i ∈ s, cartierCoefficient R (ξ i) = 0) :
    let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι
    ∃ (E : Fin q → CartierDivisor T) (hE : ∀ i, (E i).IsEffective),
      (∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T)) ∧
      ∃ (G : Fin q → CartierDivisor U) (hG : ∀ i, (G i).IsEffective),
        (∀ i ∈ s, G i = 0) ∧
        (∀ i, i ∉ s →
          effectiveCartierIdealSheaf (G i) (hG i) = (effectiveCartierIdealSheaf (E i) (hE i)).comap j ∧
          Nonempty ((Scheme.Modules.pullback j).obj (E i).sheaf ≅ (G i).sheaf) ∧
          ∀ y : U, y ∈ (effectiveCartierIdealSheaf (G i) (hG i)).support ↔
            j y ∈ closure ({ξ i} : Set T)) ∧
        let F := ∑ i ∈ sᶜ, cartierCoefficient R (ξ i) • G i
        Nonempty ((Scheme.Modules.pullback j).obj R.sheaf ≅ F.sheaf) ∧
        ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback j).obj (k • R).sheaf ≅ (k • F).sheaf) := by
  let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι
  obtain ⟨E, hE, hI, hEc, G, hG, hsel, hunselected⟩ := snc_component_exists_induced_effective_members ξ hξ hsnc s U
  obtain ⟨a⟩ := supported_cartier_induced_signed_sum_representation
    (smooth_stalk_isIntegrallyClosed (K := K)) j ξ hinj E hEc R hsupp s hzero G
    (fun i hi => (hunselected i hi).2.1)
  exact ⟨E, hE, hI, G, hG, hsel, hunselected, ⟨a⟩,
    fun k => ⟨cartierPullbackGradedIso R j _ a k⟩⟩


/-- The actual ideal dictionary fixes the prime coefficients of any chosen
SNC Cartier members; no coefficient certificate for those members is needed. -/
theorem snc_cartier_member_coefficients_of_actual_ideals
    {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
    [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [IsSeparated (T ↘ Spec (CommRingCat.of K))]
    {n q : ℕ} (ξ : Fin q → T) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (E : Fin q → CartierDivisor T) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T)) :
    ∀ (i : Fin q) (z : CodimensionOnePoint T),
      cartierCoefficient (E i) (z : T) = if (z : T) = ξ i then 1 else 0 := by
  obtain ⟨E', hE', hI', hc⟩ := exists_snc_component_cartier ξ hξ hsnc
  intro i z
  have heq := effectiveCartier_eq_of_idealSheaf_eq (E i) (E' i) (hE i) (hE' i)
    ((hI i).trans (hI' i).symm)
  rw [heq]
  exact hc i z

end MixedFujita
