/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IsolatedLCCenterSNCFibrations

/-! 元交差点から実中心射・内部次元と全倍数残余随伴。 check-298：Mathlibの消滅イデアル順像と被約源のnilradical消滅から、像包含だけで実被約閉中心へのスキーム射を内部構成。実生成点像の閉包一致から中心の生成点保存・優越性を導き、元射が固有なら中心射の固有性と全射性も供給。実SNC交差の像と全元成分閉包への所属の同値、実整開成分の生成点が交差内で極大generizationであることを証明。元の有限選択集合を内部Fin列挙し、選択SNC族・単射性・余高さ1・所属の元添字辞書・交差点での余次元上界を追加証明書なしに供給。元の孤立一意lc中心・実固有SNCモデル・任意の非空臨界選択集合から、任意の実整開閉交差成分について、正確な被約中心への実射・元射との因子化・固有性・優越性・全射性・基礎体上の可換性・生成点保存を内部構成。元モデルの各交差点から整成分自体も供給。さらに点から成分の余次元と次元を内部決定し、297の実Cartier成分・臨界係数消去・同じ残余Fの全倍数随伴を同じ実中心射へ接続。中心上の実Cartier代表Qと、元D及び中心Qの全自然数倍を同じdK_U+Fへ引き戻す実層同型まで一つの存在定理で供給。成分・中心射・像包含・優越性・次元証明書・Cartier代表・比較同型や通常KVを追加入力にしない。正値性・相対標準類評価・元中心の数値随伴・一般KV・F1F2は残る。 -/

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


/-- A genuine commuting factorization internally supplies ONE Cartier
class on the actual center and its pullback representation in ALL degrees.
No center representative or comparison with the source is supplied. -/
theorem commuting_factorization_exists_center_adjoint_representative
    {Y Z X : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] [IsIntegral X]
    (f : Y ⟶ X) (i : Z ⟶ X) (ψ : Y ⟶ Z) (hfac : ψ ≫ i = f)
    (D : CartierDivisor X) (A : CartierDivisor Y)
    (a : (Scheme.Modules.pullback f).obj D.sheaf ≅ A.sheaf) :
    ∃ Q : CartierDivisor Z,
      Nonempty ((Scheme.Modules.pullback i).obj D.sheaf ≅ Q.sheaf) ∧
      Nonempty ((Scheme.Modules.pullback ψ).obj Q.sheaf ≅ A.sheaf) ∧
      ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback ψ).obj (k • Q).sheaf ≅ (k • A).sheaf) := by
  obtain ⟨Q, ⟨aQ⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D i
  let aψ : (Scheme.Modules.pullback ψ).obj Q.sheaf ≅ A.sheaf :=
    (Scheme.Modules.pullback ψ).mapIso aQ.symm ≪≫
      (Scheme.Modules.pullbackComp ψ i).app D.sheaf ≪≫
        eqToIso (congrArg (fun g : Y ⟶ X => (Scheme.Modules.pullback g).obj D.sheaf) hfac) ≪≫ a
  exact ⟨Q, ⟨aQ⟩, ⟨aψ⟩, fun k => ⟨cartierPullbackGradedIso Q ψ A aψ k⟩⟩


/-- ORIGINAL isolated-lc and selected critical SNC geometry supply an actual
proper surjective dominant center fibration AND its canonical-plus-residual
pullback formula. The component, dimension, Cartier components, center class,
residual class and ALL-degree comparisons are internal. No KV input. -/
theorem isolated_unique_lc_center_exists_selected_adjoint_fibration_at
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
    let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    let ζ := sncSelectedPoints ξ s
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ζ) Finset.univ
    let J := Scheme.IdealSheafData.vanishingIdeal Z
    let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
    let : J.subscheme.Over (Spec (CommRingCat.of K)) := ⟨J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    let : J.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    ∃ (ℓ : ℕ) (hdim : Fintype.card s + ℓ = n)
      (U : I.subscheme.Opens) (hint : IsIntegral U)
      (hclosed : IsClosed (U : Set I.subscheme)) (_hp : p ∈ U),
      let : IsIntegral U := hint
      ∃ (E : Fin (Fintype.card s) → CartierDivisor T) (hE : ∀ k, (E k).IsEffective)
        (_hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ({ζ k} : Set T), isClosed_closure⟩ : Closeds T)),
        (∀ k, cartierCoefficient (B - d • ∑ i, E i) (ζ k) = 0) ∧
        (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ζ →
          cartierCoefficient (B - d • ∑ i, E i) (z : T) = cartierCoefficient B (z : T)) ∧
        ∃ (cU : EtaleChart K U ℓ) (hintZ : IsIntegral J.subscheme),
          let : IsIntegral J.subscheme := hintZ
          let j := U.ι ≫ I.subschemeι
          let KU := canonicalDivisor ℓ cU (snc_component_etaleChart_cover ζ
            (by simpa only [hdim] using sncSelectedPoints_isSNCFamily ξ hsnc s) E hE U hclosed)
          ∃ ψ : U.toScheme ⟶ J.subscheme,
            ψ ≫ J.subschemeι = j ≫ ρ ∧ IsProper ψ ∧ IsDominant ψ ∧ Function.Surjective ψ ∧
              ψ.IsOver (Spec (CommRingCat.of K)) ∧
              ψ (genericPoint U) = genericPoint J.subscheme ∧
              ∃ (F : CartierDivisor U) (Q : CartierDivisor J.subscheme),
                Nonempty ((Scheme.Modules.pullback j).obj (B - d • ∑ k, E k).sheaf ≅ F.sheaf) ∧
                Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj D.sheaf ≅ (d • KU + F).sheaf) ∧
                Nonempty ((Scheme.Modules.pullback J.subschemeι).obj D.sheaf ≅ Q.sheaf) ∧
                Nonempty ((Scheme.Modules.pullback ψ).obj Q.sheaf ≅ (d • KU + F).sheaf) ∧
                (∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj (k • D).sheaf ≅
                  (k • (d • KU + F)).sheaf)) ∧
                ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback ψ).obj (k • Q).sheaf ≅
                  (k • (d • KU + F)).sheaf) := by
  have hle := sncSelectedPoints_card_le_dimension_at_stratum_point ξ hsnc s p
  obtain ⟨ℓ, hℓ⟩ := Nat.exists_eq_add_of_le hle
  subst n
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (Fintype.card s + ℓ) _
  let : IsNoetherian T := properOverField_scheme_isNoetherian (K := K) (X := T)
  let ζ := sncSelectedPoints ξ s
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ζ) Finset.univ
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let : J.subscheme.Over (Spec (CommRingCat.of K)) := ⟨J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : J.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hζ := sncSelectedPoints_isSNCFamily ξ hsnc s
  obtain ⟨hζinj, hζcoh⟩ := sncSelectedPoints_injective_and_coheight ξ hinj hξ s
  have hζcrit (k : Fin (Fintype.card s)) : cartierCoefficient B (ζ k) = (d : ℤ) :=
    hcrit _ ((Fintype.equivFin s).symm k).prop
  obtain ⟨E, hE, hI, _hEc, hzero, houtside⟩ :=
    exists_snc_critical_residual_components ζ hζinj hζcoh hζ B d hζcrit
  obtain ⟨U, _W, hpU, _hpW, _hWU, hclosed, hint, _hj⟩ :=
    snc_stratum_exists_lifted_integral_component ζ hζ p
  let := hint
  have hcover := snc_component_etaleChart_cover ζ hζ E hE U hclosed
  have hgeneric : genericPoint U ∈ iSup (fun c : EtaleChart K U ℓ => c.U) := by
    rw [hcover]
    trivial
  obtain ⟨cU, _hcU⟩ := Opens.mem_iSup.mp hgeneric
  obtain ⟨hintZ, ψ, hψ, hproper, hdom, hsurj, hover, hmap⟩ :=
    isolated_unique_lc_center_selected_component_proper_fibration ρ hρ hnorm c f d hd D
      hlc Z hunique hNK H hH cT ξ hinj hξ hsnc hsupp s hs hcrit U hclosed
  let := hintZ
  let j := U.ι ≫ I.subschemeι
  let KU := canonicalDivisor ℓ cU hcover
  obtain ⟨F, ⟨aF⟩, ⟨aD⟩, hDgrades⟩ :=
    crepant_snc_component_adjoint_restriction_representation ζ E U hclosed hζ hE hI
      cT etaleCharts_cover cU ρ hρ c f H D hH d
  obtain ⟨Q, aQ, aψ, hQgrades⟩ :=
    commuting_factorization_exists_center_adjoint_representative (j ≫ ρ) J.subschemeι ψ hψ
      D (d • KU + F) aD
  exact ⟨ℓ, rfl, U, hint, hclosed, hpU, E, hE, hI, hzero, houtside, cU, hintZ,
    ψ, hψ, hproper, hdom, hsurj, hover, hmap, F, Q, ⟨aF⟩, ⟨aD⟩, aQ, aψ, hDgrades, hQgrades⟩

end MixedFujita
