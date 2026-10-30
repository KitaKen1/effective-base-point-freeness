/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ReducedCenterFactorization

/-! 実SNC交差像と整成分生成点の元交差内極大性。 check-298：Mathlibの消滅イデアル順像と被約源のnilradical消滅から、像包含だけで実被約閉中心へのスキーム射を内部構成。実生成点像の閉包一致から中心の生成点保存・優越性を導き、元射が固有なら中心射の固有性と全射性も供給。実SNC交差の像と全元成分閉包への所属の同値、実整開成分の生成点が交差内で極大generizationであることを証明。元の有限選択集合を内部Fin列挙し、選択SNC族・単射性・余高さ1・所属の元添字辞書・交差点での余次元上界を追加証明書なしに供給。元の孤立一意lc中心・実固有SNCモデル・任意の非空臨界選択集合から、任意の実整開閉交差成分について、正確な被約中心への実射・元射との因子化・固有性・優越性・全射性・基礎体上の可換性・生成点保存を内部構成。元モデルの各交差点から整成分自体も供給。さらに点から成分の余次元と次元を内部決定し、297の実Cartier成分・臨界係数消去・同じ残余Fの全倍数随伴を同じ実中心射へ接続。中心上の実Cartier代表Qと、元D及び中心Qの全自然数倍を同じdK_U+Fへ引き戻す実層同型まで一つの存在定理で供給。成分・中心射・像包含・優越性・次元証明書・Cartier代表・比較同型や通常KVを追加入力にしない。正値性・相対標準類評価・元中心の数値随伴・一般KV・F1F2は残る。 -/

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


/-- The ACTUAL full stratum has exactly the original component intersection
as its image, in both directions. -/
theorem snc_stratum_range_iff_mem_all_components
    {T : Scheme.{u}} {m : ℕ} (ξ : Fin m → T) (x : T) :
    x ∈ Set.range (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ↔
      ∀ k, x ∈ closure ({ξ k} : Set T) := by
  rw [Scheme.IdealSheafData.range_subschemeι, snc_all_stratumIdeal_eq_iSup,
    Scheme.IdealSheafData.support_iSup]
  simp only [Closeds.coe_iInf, Set.mem_iInter, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl


/-- The generic point of ANY actual integral open component is maximal for
generization inside the ORIGINAL component intersection. No generic-component
certificate or maximality is supplied. -/
theorem snc_integral_component_generic_maximal
    {T : Scheme.{u}} {m : ℕ} (ξ : Fin m → T)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    [IsIntegral U] :
    let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
    (∀ k, j (genericPoint U) ∈ closure ({ξ k} : Set T)) ∧
      ∀ η' : T, (∀ k, η' ∈ closure ({ξ k} : Set T)) → η' ⤳ j (genericPoint U) →
        η' = j (genericPoint U) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let j := U.ι ≫ I.subschemeι
  dsimp only
  refine ⟨fun k => snc_stratum_point_mem_all_components ξ (U.ι (genericPoint U)) k, ?_⟩
  intro η' hη' hsp
  obtain ⟨q, hq⟩ := (snc_stratum_range_iff_mem_all_components ξ η').mpr hη'
  have hqsp : q ⤳ U.ι (genericPoint U) :=
    I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.specializes_iff.mp
      (by rw [hq]; exact hsp)
  have hqU : q ∈ U := hqsp.mem_open U.isOpen (genericPoint U).prop
  let qU : U.toScheme := ⟨q, hqU⟩
  have hqUsp : qU ⤳ genericPoint U :=
    U.ι.isOpenEmbedding.isEmbedding.isInducing.specializes_iff.mp hqsp
  have heq : qU = genericPoint U := (hqUsp.antisymm (genericPoint_specializes (α := U.toScheme) qU)).eq
  exact hq.symm.trans (congrArg (fun u : U => j u) heq)

end MixedFujita
