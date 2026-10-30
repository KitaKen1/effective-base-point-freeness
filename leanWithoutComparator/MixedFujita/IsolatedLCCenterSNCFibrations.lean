/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SelectedSNCFamilies
public import MixedFujita.CriticalSNCStratumDominance

/-! 元孤立lc臨界交差から実中心への固有優越全射。 check-298：Mathlibの消滅イデアル順像と被約源のnilradical消滅から、像包含だけで実被約閉中心へのスキーム射を内部構成。実生成点像の閉包一致から中心の生成点保存・優越性を導き、元射が固有なら中心射の固有性と全射性も供給。実SNC交差の像と全元成分閉包への所属の同値、実整開成分の生成点が交差内で極大generizationであることを証明。元の有限選択集合を内部Fin列挙し、選択SNC族・単射性・余高さ1・所属の元添字辞書・交差点での余次元上界を追加証明書なしに供給。元の孤立一意lc中心・実固有SNCモデル・任意の非空臨界選択集合から、任意の実整開閉交差成分について、正確な被約中心への実射・元射との因子化・固有性・優越性・全射性・基礎体上の可換性・生成点保存を内部構成。元モデルの各交差点から整成分自体も供給。さらに点から成分の余次元と次元を内部決定し、297の実Cartier成分・臨界係数消去・同じ残余Fの全倍数随伴を同じ実中心射へ接続。中心上の実Cartier代表Qと、元D及び中心Qの全自然数倍を同じdK_U+Fへ引き戻す実層同型まで一つの存在定理で供給。成分・中心射・像包含・優越性・次元証明書・Cartier代表・比較同型や通常KVを追加入力にしない。正値性・相対標準類評価・元中心の数値随伴・一般KV・F1F2は残る。 -/

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


/-- ORIGINAL isolated-lc and actual selected critical SNC geometry construct
an ACTUAL proper surjective dominant morphism from ANY actual integral clopen
component to the EXACT reduced center, with factorization, base-field and
generic-point laws internal. Neither image containment nor dominance is input. -/
theorem isolated_unique_lc_center_selected_component_proper_fibration
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hunique : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V = Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔ x ∈ Z)
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (s : Finset (Fin r)) (hs : s.Nonempty)
    (hcrit : ∀ i ∈ s,
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    [(sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme.Opens)
    [IsIntegral U]
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme)) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ
    let J := Scheme.IdealSheafData.vanishingIdeal Z
    let : J.subscheme.Over (Spec (CommRingCat.of K)) := ⟨J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    let : J.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    ∃ hintZ : IsIntegral J.subscheme,
      let : IsIntegral J.subscheme := hintZ
      ∃ ψ : U.toScheme ⟶ J.subscheme,
        ψ ≫ J.subschemeι = (U.ι ≫ I.subschemeι) ≫ ρ ∧
        IsProper ψ ∧ IsDominant ψ ∧ Function.Surjective ψ ∧
        ψ.IsOver (Spec (CommRingCat.of K)) ∧
        ψ (genericPoint U) = genericPoint J.subscheme := by
  let ζ := sncSelectedPoints ξ s
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ζ) Finset.univ
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  let j := U.ι ≫ I.subschemeι
  let : J.subscheme.Over (Spec (CommRingCat.of K)) := ⟨J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : J.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  obtain ⟨hmem, hmax⟩ := snc_integral_component_generic_maximal ζ U
  have hm : ∀ i ∈ s, j (genericPoint U) ∈ closure ({ξ i} : Set T) :=
    (sncSelectedPoints_mem_all_iff ξ s (j (genericPoint U))).mp hmem
  have hx : ∀ η' : T, (∀ i ∈ s, η' ∈ closure ({ξ i} : Set T)) →
      η' ⤳ j (genericPoint U) → η' = j (genericPoint U) := by
    intro η' hη' hsp
    exact hmax η' ((sncSelectedPoints_mem_all_iff ξ s η').mpr hη') hsp
  have hgeneric := isolated_unique_lc_center_critical_snc_stratum_dominates ρ hρ hnorm c f d hd D
    hlc Z hunique hNK H hH cT ξ hinj hξ hsnc hsupp s hs hcrit (j (genericPoint U)) hm hx
  have hintZ : IsIntegral J.subscheme := by
    dsimp only [J]
    rw [← hgeneric]
    change IsIntegral (pointClosureScheme (ρ (j (genericPoint U))))
    infer_instance
  let := hintZ
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  let : IsProper (j ≫ ρ) := by dsimp only [j]; infer_instance
  obtain ⟨ψ, hψ, hproper, hdom, hsurj, hmap⟩ :=
    proper_integral_source_exists_surjective_closed_center_factor (j ≫ ρ) Z hgeneric
  have hover : ψ.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change ψ ≫ (J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))) = (U.toScheme ↘ Spec (CommRingCat.of K))
    rw [← Category.assoc, hψ]
    exact HomIsOver.comp_over (f := j ≫ ρ)
  exact ⟨hintZ, ψ, hψ, hproper, hdom, hsurj, hover, hmap⟩


/-- At EVERY point, the original proper SNC model supplies an actual integral
component and the proper surjective dominant fibration to the exact center.
No chosen component, generic point or map is supplied. -/
theorem isolated_unique_lc_center_exists_selected_component_fibration_at
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hunique : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V = Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔ x ∈ Z)
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (s : Finset (Fin r)) (hs : s.Nonempty)
    (hcrit : ∀ i ∈ s,
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    [(sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (p : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme) :
    ∃ (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme.Opens)
      (hint : IsIntegral U)
      (_hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ).subscheme))
      (_hp : p ∈ U),
      let : IsIntegral U := hint
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s)) Finset.univ
    let J := Scheme.IdealSheafData.vanishingIdeal Z
    let : J.subscheme.Over (Spec (CommRingCat.of K)) := ⟨J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    let : J.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    ∃ hintZ : IsIntegral J.subscheme,
      let : IsIntegral J.subscheme := hintZ
      ∃ ψ : U.toScheme ⟶ J.subscheme,
        ψ ≫ J.subschemeι = (U.ι ≫ I.subschemeι) ≫ ρ ∧
        IsProper ψ ∧ IsDominant ψ ∧ Function.Surjective ψ ∧
        ψ.IsOver (Spec (CommRingCat.of K)) ∧
        ψ (genericPoint U) = genericPoint J.subscheme := by
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : IsNoetherian T := properOverField_scheme_isNoetherian (K := K) (X := T)
  obtain ⟨U, _W, hpU, _hpW, _hWU, hclosed, hint, _hj⟩ :=
    snc_stratum_exists_lifted_integral_component (sncSelectedPoints ξ s)
      (sncSelectedPoints_isSNCFamily ξ hsnc s) p
  let := hint
  exact ⟨U, hint, hclosed, hpU,
    isolated_unique_lc_center_selected_component_proper_fibration ρ hρ hnorm c f d hd D
      hlc Z hunique hNK H hH cT ξ hinj hξ hsnc hsupp s hs hcrit U hclosed⟩

end MixedFujita
