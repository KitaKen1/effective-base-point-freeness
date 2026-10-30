/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AllCriticalRemovedSNCResidual

/-! 実標準切断の正確な非消失開と台外像引き戻し自明性。 check-299：元の非空交差と許された有限成分集合から、有限powerset上の最大濃度選択で包含最大の非空交差を内部構成し、残る許容成分が交差全体と非接触であることを証明。元の臨界係数と一つの実選択交差点から、種選択を含む最大臨界選択・その実交差点・全選択外臨界成分の交差全体からの回避を内部供給。元lcの全モデル係数上界と実SNC成分Cartier辞書から、全臨界成分を同時に除いた実残余Rを構成し、全SNC係数<d・支持保存・同じ周囲モデル上の実全モデルklt対を証明。実有効Cartier因子の標準切断について零因子が元因子そのもの、非消失開が実イデアル台の補集合であることを証明し、像が台を避ける任意射の実引き戻しを追加切断・自明化なしに自明化。有限和・全倍数・実テンソル同型を用い、選択外臨界因子が非接触なら、選択臨界除去と全臨界除去の実残余引き戻し層が同型であることを証明。最後に元孤立一意lc中心・実固有SNCモデル・種臨界交差点から、最大選択・内部次元・実整成分・正確な中心への固有優越全射・元モデル上のklt残余R・同じ成分残余F及び中心Q・元DとQの全自然数倍随伴を一括内部供給する存在定理へ接続。最大性・回避・klt残余・非消失切断・自明化・比較同型・通常KVを入力にしない。kltは周囲モデル上の全臨界除去残余について証明した範囲で、任意に選んだ成分Cartier代表Fの係数や成分上kltはまだ主張しない。成分境界の実SNC係数表示・相対正値性・元中心数値随伴・一般KV・F1F2は残る。 -/

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


/-- The canonical section of an effective Cartier divisor has exactly that
ACTUAL zero divisor and is nonvanishing exactly off its ACTUAL ideal support. -/
theorem effectiveCartier_exists_canonical_section_with_exact_nonvanishing
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (E : CartierDivisor X) (hE : E.IsEffective) :
    ∃ (s : Γ(E.sheaf, ⊤)) (hs : s ≠ 0), cartierSectionZeroDivisor E s hs = E ∧
      ∀ x : X, x ∈ cartierSectionNonvanishingOpen E s ↔
        x ∉ (effectiveCartierIdealSheaf E hE).support := by
  let s := Scheme.Modules.Hom.app (E.unitToSheaf hE) ⊤ (1 : Γ(X, ⊤))
  have hval : cartierSectionRational E s = 1 := by
    rw [cartierSectionRational_apply]
    dsimp only [s]
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, E.unitToSheaf_ι,
      Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one]
  have hs : s ≠ 0 := by
    intro h
    have hz := hval
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have hu : cartierSectionUnit E s hs = 1 := Units.ext hval
  have hz : cartierSectionZeroDivisor E s hs = E := by
    simp only [cartierSectionZeroDivisor, hu, principalCartierDivisor_one, add_zero]
  have hsupport : ((effectiveCartierIdealSheaf E hE).support : Set X) = cartierSectionZeroLocus E s := by
    have h := cartierSectionZeroIdeal_support (K := K) E s hs
    change ((effectiveCartierIdealSheaf (cartierSectionZeroDivisor E s hs) _).support : Set X) = _ at h
    simpa only [hz] using h
  refine ⟨s, hs, hz, ?_⟩
  intro x
  change (x ∈ cartierSectionNonvanishingOpen E s) ↔ x ∉ ((effectiveCartierIdealSheaf E hE).support : Set X)
  rw [hsupport]
  change (x ∈ cartierSectionNonvanishingOpen E s) ↔ ¬¬ (x ∈ cartierSectionNonvanishingOpen E s)
  exact (not_not).symm


/-- If an ACTUAL morphism misses the ACTUAL support of an effective Cartier
divisor, its module pullback is trivial. No section or trivialization is input. -/
theorem effectiveCartier_pullback_trivial_of_image_off_support
    {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] (E : CartierDivisor X) (hE : E.IsEffective) (φ : Y ⟶ X)
    (h : ∀ y : Y, φ y ∉ (effectiveCartierIdealSheaf E hE).support) :
    Nonempty ((Scheme.Modules.pullback φ).obj E.sheaf ≅ (0 : CartierDivisor Y).sheaf) := by
  obtain ⟨s, _hs, _hz, hsupp⟩ := effectiveCartier_exists_canonical_section_with_exact_nonvanishing (K := K) E hE
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor E φ
  obtain ⟨f, hf⟩ := cartierPullback_representation_principal_of_image_nonvanishing E φ A a s
    (fun y => (hsupp (φ y)).mpr (h y))
  exact ⟨a ≪≫ eqToIso (congrArg CartierDivisor.sheaf hf) ≪≫
    (CartierDivisor.unitIsoSheafPrincipalCartierDivisor Y f).symm ≪≫ (cartierZeroSheafIso Y).symm⟩

end MixedFujita
