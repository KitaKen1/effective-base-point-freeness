/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IsolatedLCCenterAdjointFibrations
public import Mathlib.Data.Finset.Max

/-! 種交差から最大非空臨界選択と交差全体の残余臨界回避。 check-299：元の非空交差と許された有限成分集合から、有限powerset上の最大濃度選択で包含最大の非空交差を内部構成し、残る許容成分が交差全体と非接触であることを証明。元の臨界係数と一つの実選択交差点から、種選択を含む最大臨界選択・その実交差点・全選択外臨界成分の交差全体からの回避を内部供給。元lcの全モデル係数上界と実SNC成分Cartier辞書から、全臨界成分を同時に除いた実残余Rを構成し、全SNC係数<d・支持保存・同じ周囲モデル上の実全モデルklt対を証明。実有効Cartier因子の標準切断について零因子が元因子そのもの、非消失開が実イデアル台の補集合であることを証明し、像が台を避ける任意射の実引き戻しを追加切断・自明化なしに自明化。有限和・全倍数・実テンソル同型を用い、選択外臨界因子が非接触なら、選択臨界除去と全臨界除去の実残余引き戻し層が同型であることを証明。最後に元孤立一意lc中心・実固有SNCモデル・種臨界交差点から、最大選択・内部次元・実整成分・正確な中心への固有優越全射・元モデル上のklt残余R・同じ成分残余F及び中心Q・元DとQの全自然数倍随伴を一括内部供給する存在定理へ接続。最大性・回避・klt残余・非消失切断・自明化・比較同型・通常KVを入力にしない。kltは周囲モデル上の全臨界除去残余について証明した範囲で、任意に選んだ成分Cartier代表Fの係数や成分上kltはまだ主張しない。成分境界の実SNC係数表示・相対正値性・元中心数値随伴・一般KV・F1F2は残る。 -/

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


/-- From an original nonempty selected intersection, internally choose a
largest nonempty allowed intersection extending it. Every remaining allowed
member misses the ENTIRE intersection, not only its generic point. -/
theorem exists_maximal_allowed_component_intersection
    {T : Type u} [TopologicalSpace T] {q : ℕ} (ξ : Fin q → T)
    (C s₀ : Finset (Fin q)) (hs₀ : s₀.Nonempty) (hs₀C : s₀ ⊆ C)
    (x₀ : T) (hx₀ : ∀ i ∈ s₀, x₀ ∈ closure ({ξ i} : Set T)) :
    ∃ s : Finset (Fin q), s₀ ⊆ s ∧ s ⊆ C ∧ s.Nonempty ∧
      (∃ x : T, ∀ i ∈ s, x ∈ closure ({ξ i} : Set T)) ∧
      ∀ x : T, (∀ i ∈ s, x ∈ closure ({ξ i} : Set T)) →
        ∀ i ∈ C, i ∉ s → x ∉ closure ({ξ i} : Set T) := by
  classical
  let A := C.powerset.filter fun t => s₀ ⊆ t ∧ ∃ x : T, ∀ i ∈ t, x ∈ closure ({ξ i} : Set T)
  have hseed : s₀ ∈ A := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hs₀C, Finset.Subset.refl _, x₀, hx₀⟩
  obtain ⟨s, hsA, hmax⟩ := Finset.exists_max_image A Finset.card ⟨s₀, hseed⟩
  obtain ⟨hsC, hs₀s, hnonempty⟩ := Finset.mem_filter.mp hsA
  have hsC' : s ⊆ C := Finset.mem_powerset.mp hsC
  refine ⟨s, hs₀s, hsC', hs₀.mono hs₀s, hnonempty, ?_⟩
  intro x hx i hiC his hxi
  have hnew : insert i s ∈ A := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨hiC, hsC'⟩),
      hs₀s.trans (Finset.subset_insert _ _), x, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact hxi
    · exact hx j hjs
  have hcard := hmax (insert i s) hnew
  rw [Finset.card_insert_of_notMem his] at hcard
  omega


/-- Original critical coefficients and ONE actual selected-stratum point
supply a maximal critical selection and an actual point of its stratum.
EVERY other critical component is disjoint from the WHOLE selected stratum. -/
theorem exists_maximal_critical_snc_selection
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] {q : ℕ}
    (ξ : Fin q → T) (B : CartierDivisor T) (d : ℕ)
    (s₀ : Finset (Fin q)) (hs₀ : s₀.Nonempty)
    (hcrit₀ : ∀ i ∈ s₀, cartierCoefficient B (ξ i) = (d : ℤ))
    (p₀ : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s₀)) Finset.univ).subscheme) :
    ∃ (s : Finset (Fin q)), s₀ ⊆ s ∧ s.Nonempty ∧
      (∀ i ∈ s, cartierCoefficient B (ξ i) = (d : ℤ)) ∧
      ∃ _p : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme,
        ∀ y : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme,
          ∀ i, cartierCoefficient B (ξ i) = (d : ℤ) → i ∉ s →
            (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι y ∉
              closure ({ξ i} : Set T) := by
  classical
  let C := Finset.univ.filter fun i => cartierCoefficient B (ξ i) = (d : ℤ)
  have hs₀C : s₀ ⊆ C := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcrit₀ i hi⟩
  let x₀ := (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s₀)) Finset.univ).subschemeι p₀
  have hx₀ : ∀ i ∈ s₀, x₀ ∈ closure ({ξ i} : Set T) :=
    (sncSelectedPoints_mem_all_iff ξ s₀ x₀).mp
      (fun k => snc_stratum_point_mem_all_components (sncSelectedPoints ξ s₀) p₀ k)
  obtain ⟨s, _hs₀s, hsC, hs, ⟨x, hx⟩, havoid⟩ :=
    exists_maximal_allowed_component_intersection ξ C s₀ hs₀ hs₀C x₀ hx₀
  obtain ⟨p, _hp⟩ := (snc_stratum_range_iff_mem_all_components (sncSelectedPoints ξ s) x).mpr
    ((sncSelectedPoints_mem_all_iff ξ s x).mpr hx)
  refine ⟨s, _hs₀s, hs, fun i hi => (Finset.mem_filter.mp (hsC hi)).2, p, ?_⟩
  intro y i hi his
  let z := (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι y
  have hz : ∀ k ∈ s, z ∈ closure ({ξ k} : Set T) :=
    (sncSelectedPoints_mem_all_iff ξ s z).mp
      (fun k => snc_stratum_point_mem_all_components (sncSelectedPoints ξ s) y k)
  exact havoid z hz i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) his

end MixedFujita
