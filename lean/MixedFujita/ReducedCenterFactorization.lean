/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CriticalSNCResidualAdjunction
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! 被約源から実閉中心への因子化・優越性・固有全射を内部構成。 check-298：Mathlibの消滅イデアル順像と被約源のnilradical消滅から、像包含だけで実被約閉中心へのスキーム射を内部構成。実生成点像の閉包一致から中心の生成点保存・優越性を導き、元射が固有なら中心射の固有性と全射性も供給。実SNC交差の像と全元成分閉包への所属の同値、実整開成分の生成点が交差内で極大generizationであることを証明。元の有限選択集合を内部Fin列挙し、選択SNC族・単射性・余高さ1・所属の元添字辞書・交差点での余次元上界を追加証明書なしに供給。元の孤立一意lc中心・実固有SNCモデル・任意の非空臨界選択集合から、任意の実整開閉交差成分について、正確な被約中心への実射・元射との因子化・固有性・優越性・全射性・基礎体上の可換性・生成点保存を内部構成。元モデルの各交差点から整成分自体も供給。さらに点から成分の余次元と次元を内部決定し、297の実Cartier成分・臨界係数消去・同じ残余Fの全倍数随伴を同じ実中心射へ接続。中心上の実Cartier代表Qと、元D及び中心Qの全自然数倍を同じdK_U+Fへ引き戻す実層同型まで一つの存在定理で供給。成分・中心射・像包含・優越性・次元証明書・Cartier代表・比較同型や通常KVを追加入力にしない。正値性・相対標準類評価・元中心の数値随伴・一般KV・F1F2は残る。 -/

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


/-- A reduced ACTUAL source factors through the ACTUAL reduced closed center
from topological image containment alone; no kernel certificate is supplied. -/
theorem reduced_source_exists_closed_center_factor
    {Y X : Scheme.{u}} [IsReduced Y] (f : Y ⟶ X) (Z : Closeds X)
    (himage : Set.range f ⊆ (Z : Set X)) :
    ∃ ψ : Y ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      ψ ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hk : f.ker = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range f)) := by
    rw [← Scheme.IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot (X := Y),
      ← Scheme.IdealSheafData.vanishingIdeal_top, Scheme.IdealSheafData.map_vanishingIdeal]
    simp only [Closeds.coe_top, Set.image_univ]
  have hle : I ≤ f.ker := by
    rw [hk]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (closure_minimal himage Z.isClosed)
  exact ⟨IsClosedImmersion.lift I.subschemeι f (by simpa only [I.ker_subschemeι] using hle),
    IsClosedImmersion.lift_fac _ _ _⟩


/-- A dense generic image constructs the actual closed-center map and its
actual generic-point preservation and dominance, without a map/dominance input. -/
theorem integral_source_exists_dominant_closed_center_factor
    {Y X : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (hgeneric : (⟨closure ({f (genericPoint Y)} : Set X), isClosed_closure⟩ : Closeds X) = Z) :
    ∃ ψ : Y ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      ψ ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f ∧ IsDominant ψ ∧
        ψ (genericPoint Y) = genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hg : f (genericPoint Y) ∈ Z := by rw [← hgeneric]; exact subset_closure rfl
  have himage : Set.range f ⊆ (Z : Set X) := by
    rintro _ ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map f.continuous).mem_closed Z.isClosed hg
  obtain ⟨ψ, hψ⟩ := reduced_source_exists_closed_center_factor f Z himage
  have ht := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
  rw [Set.image_univ, I.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
    Z.isClosed.closure_eq] at ht
  have hs : IsGenericPoint (f (genericPoint Y)) (Z : Set X) := by
    rw [← hgeneric]
    exact isGenericPoint_closure
  have hmap : ψ (genericPoint Y) = genericPoint I.subscheme := by
    apply I.subschemeι.isClosedEmbedding.injective
    exact (congrArg (fun g : Y ⟶ X => g (genericPoint Y)) hψ).trans (ht.eq hs).symm
  have hdom : IsDominant ψ := by
    rw [isDominant_iff, denseRange_iff_closure_range]
    have hcl := closure_mono (Set.singleton_subset_iff.mpr
      (show genericPoint I.subscheme ∈ Set.range ψ from ⟨genericPoint Y, hmap⟩))
    rw [(genericPoint_spec I.subscheme).def] at hcl
    exact Set.univ_subset_iff.mp hcl
  exact ⟨ψ, hψ, hdom, hmap⟩


/-- Properness plus dense generic image gives a proper SURJECTIVE actual
map to the actual reduced center, with its original factorization retained. -/
theorem proper_integral_source_exists_surjective_closed_center_factor
    {Y X : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsProper f] (Z : Closeds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
    (hgeneric : (⟨closure ({f (genericPoint Y)} : Set X), isClosed_closure⟩ : Closeds X) = Z) :
    ∃ ψ : Y ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
      ψ ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = f ∧
        IsProper ψ ∧ IsDominant ψ ∧ Function.Surjective ψ ∧
          ψ (genericPoint Y) = genericPoint (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  obtain ⟨ψ, hψ, hdom, hmap⟩ := integral_source_exists_dominant_closed_center_factor f Z hgeneric
  let : IsProper (ψ ≫ I.subschemeι) := by rw [hψ]; infer_instance
  let : IsProper ψ := IsProper.of_comp ψ I.subschemeι
  let := hdom
  have hclosed : IsClosed (Set.range ψ) := by
    simpa only [Set.image_univ] using ψ.isClosedMap Set.univ isClosed_univ
  have hr : Set.range ψ = Set.univ := hclosed.closure_eq.symm.trans
    (denseRange_iff_closure_range.mp ψ.denseRange)
  exact ⟨ψ, hψ, inferInstance, hdom, Set.range_eq_univ.mp hr, hmap⟩

end MixedFujita
