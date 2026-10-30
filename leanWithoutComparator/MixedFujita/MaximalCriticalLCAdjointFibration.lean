/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCResidualCriticalErasure

/-! 元孤立lcから最大臨界・周囲klt残余・同じ中心射と全倍数随伴。 check-299：元の非空交差と許された有限成分集合から、有限powerset上の最大濃度選択で包含最大の非空交差を内部構成し、残る許容成分が交差全体と非接触であることを証明。元の臨界係数と一つの実選択交差点から、種選択を含む最大臨界選択・その実交差点・全選択外臨界成分の交差全体からの回避を内部供給。元lcの全モデル係数上界と実SNC成分Cartier辞書から、全臨界成分を同時に除いた実残余Rを構成し、全SNC係数<d・支持保存・同じ周囲モデル上の実全モデルklt対を証明。実有効Cartier因子の標準切断について零因子が元因子そのもの、非消失開が実イデアル台の補集合であることを証明し、像が台を避ける任意射の実引き戻しを追加切断・自明化なしに自明化。有限和・全倍数・実テンソル同型を用い、選択外臨界因子が非接触なら、選択臨界除去と全臨界除去の実残余引き戻し層が同型であることを証明。最後に元孤立一意lc中心・実固有SNCモデル・種臨界交差点から、最大選択・内部次元・実整成分・正確な中心への固有優越全射・元モデル上のklt残余R・同じ成分残余F及び中心Q・元DとQの全自然数倍随伴を一括内部供給する存在定理へ接続。最大性・回避・klt残余・非消失切断・自明化・比較同型・通常KVを入力にしない。kltは周囲モデル上の全臨界除去残余について証明した範囲で、任意に選んだ成分Cartier代表Fの係数や成分上kltはまだ主張しない。成分境界の実SNC係数表示・相対正値性・元中心数値随伴・一般KV・F1F2は残る。 -/

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


/-- ORIGINAL isolated-lc geometry and one nonempty critical intersection
internally choose a maximal critical stratum, an actual center fibration,
ALL-critical-removed ambient sub-klt residual, and the SAME all-degree
adjoint representation after erasing disjoint unselected critical factors.
No maximality, avoidance, residual klt, trivialization or comparison input. -/
theorem isolated_unique_lc_center_exists_maximal_critical_subklt_adjoint_fibration
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
    (s₀ : Finset (Fin r)) (hs₀ : s₀.Nonempty)
    (hcrit₀ : ∀ i ∈ s₀,
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    (p₀ : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ s₀)) Finset.univ).subscheme) :
    let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
    let C := Finset.univ.filter fun i => cartierCoefficient B (ξ i) = (d : ℤ)
    let J := Scheme.IdealSheafData.vanishingIdeal Z
    let : J.subscheme.Over (Spec (CommRingCat.of K)) := ⟨J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    let : J.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    ∃ s : Finset (Fin r), s₀ ⊆ s ∧ s.Nonempty ∧
      (∀ i ∈ s, cartierCoefficient B (ξ i) = (d : ℤ)) ∧
      let ζ := sncSelectedPoints ξ s
      let I := sncStratumIdeal (sncDivisorFamilyOfPoints ζ) Finset.univ
      let : I.subscheme.Over (Spec (CommRingCat.of K)) := ⟨I.subschemeι ≫ (T ↘ Spec (CommRingCat.of K))⟩
      let : I.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      ∃ (ℓ : ℕ) (hdim : Fintype.card s + ℓ = n)
        (U : I.subscheme.Opens) (hint : IsIntegral U) (hclosed : IsClosed (U : Set I.subscheme))
        (E : Fin r → CartierDivisor T) (hE : ∀ i, (E i).IsEffective)
        (_hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
          (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T)),
        let : IsIntegral U := hint
        let R := B - d • ∑ i ∈ C, E i
        let j := U.ι ≫ I.subschemeι
        (∀ i, cartierCoefficient R (ξ i) < (d : ℤ)) ∧
        (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient R (z : T) = 0) ∧
        LogPairIsKlt cT 1 d (d • smoothCanonicalDivisor cT + R) ∧
        (∀ i ∈ C, i ∉ s → ∀ y : U.toScheme, j y ∉ closure ({ξ i} : Set T)) ∧
        ∃ (cU : EtaleChart K U ℓ) (hintZ : IsIntegral J.subscheme),
          let : IsIntegral J.subscheme := hintZ
          let KU := canonicalDivisor ℓ cU (snc_component_etaleChart_cover ζ
            (by simpa only [hdim] using sncSelectedPoints_isSNCFamily ξ hsnc s)
            (fun k => E ((Fintype.equivFin s).symm k).val)
            (fun k => hE ((Fintype.equivFin s).symm k).val) U hclosed)
          ∃ ψ : U.toScheme ⟶ J.subscheme,
            ψ ≫ J.subschemeι = j ≫ ρ ∧ IsProper ψ ∧ IsDominant ψ ∧ Function.Surjective ψ ∧
              ψ.IsOver (Spec (CommRingCat.of K)) ∧
              ψ (genericPoint U) = genericPoint J.subscheme ∧
              ∃ (F : CartierDivisor U) (Q : CartierDivisor J.subscheme),
                Nonempty ((Scheme.Modules.pullback j).obj R.sheaf ≅ F.sheaf) ∧
                Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj D.sheaf ≅ (d • KU + F).sheaf) ∧
                Nonempty ((Scheme.Modules.pullback J.subschemeι).obj D.sheaf ≅ Q.sheaf) ∧
                Nonempty ((Scheme.Modules.pullback ψ).obj Q.sheaf ≅ (d • KU + F).sheaf) ∧
                (∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj (k • D).sheaf ≅
                  (k • (d • KU + F)).sheaf)) ∧
                ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback ψ).obj (k • Q).sheaf ≅
                  (k • (d • KU + F)).sheaf) := by
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : IsNoetherian T := properOverField_scheme_isNoetherian (K := K) (X := T)
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let C := Finset.univ.filter fun i => cartierCoefficient B (ξ i) = (d : ℤ)
  let J := Scheme.IdealSheafData.vanishingIdeal Z
  let : J.subscheme.Over (Spec (CommRingCat.of K)) := ⟨J.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : J.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  obtain ⟨E, hE, hI, _hEc, hstrict, hRsupp, hRklt⟩ :=
    original_lc_snc_exists_all_critical_removed_klt_residual ρ hρ c f d hd D hlc cT ξ hinj hξ hsnc hsupp
  let R := B - d • ∑ i ∈ C, E i
  obtain ⟨s, hs₀s, hs, hcrit, p, havoid⟩ :=
    exists_maximal_critical_snc_selection ξ B d s₀ hs₀ hcrit₀ p₀
  let ζ := sncSelectedPoints ξ s
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ζ) Finset.univ
  let : I.subscheme.Over (Spec (CommRingCat.of K)) := ⟨I.subschemeι ≫ (T ↘ Spec (CommRingCat.of K))⟩
  let : I.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hle := sncSelectedPoints_card_le_dimension_at_stratum_point ξ hsnc s p
  obtain ⟨ℓ, hℓ⟩ := Nat.exists_eq_add_of_le hle
  subst n
  have hζ := sncSelectedPoints_isSNCFamily ξ hsnc s
  obtain ⟨U, _W, _hpU, _hpW, _hWU, hclosed, hint, _hj⟩ :=
    snc_stratum_exists_lifted_integral_component ζ hζ p
  let := hint
  let j := U.ι ≫ I.subschemeι
  let Es : Fin (Fintype.card s) → CartierDivisor T := fun k => E ((Fintype.equivFin s).symm k).val
  have hEs (k : Fin (Fintype.card s)) : (Es k).IsEffective := hE _
  have hIs (k : Fin (Fintype.card s)) : effectiveCartierIdealSheaf (Es k) (hEs k) =
      Scheme.IdealSheafData.vanishingIdeal (⟨closure ({ζ k} : Set T), isClosed_closure⟩ : Closeds T) := hI _
  have hcover := snc_component_etaleChart_cover ζ hζ Es hEs U hclosed
  have hgeneric : genericPoint U ∈ iSup (fun c : EtaleChart K U ℓ => c.U) := by
    rw [hcover]
    trivial
  obtain ⟨cU, _hcU⟩ := Opens.mem_iSup.mp hgeneric
  obtain ⟨hintZ, ψ, hψ, hproper, hdom, hsurj, hover, hmap⟩ :=
    isolated_unique_lc_center_selected_component_proper_fibration ρ hρ hnorm c f d hd D
      hlc Z hunique hNK H hH cT ξ hinj hξ hsnc hsupp s hs hcrit U hclosed
  let := hintZ
  let KU := canonicalDivisor ℓ cU hcover
  obtain ⟨F, ⟨aF⟩, ⟨aD⟩, hDgrades⟩ :=
    crepant_snc_component_adjoint_restriction_representation ζ Es U hclosed hζ hEs hIs
      cT etaleCharts_cover cU ρ hρ c f H D hH d
  have hsC : s ⊆ C := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcrit i hi⟩
  have hmiss (i : Fin r) (hi : i ∈ C) (his : i ∉ s) (y : U.toScheme) :
      j y ∉ (effectiveCartierIdealSheaf (E i) (hE i)).support := by
    change j y ∉ ((effectiveCartierIdealSheaf (E i) (hE i)).support : Set T)
    rw [hI i, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact havoid (U.ι y) i (Finset.mem_filter.mp hi).2 his
  obtain ⟨aErase⟩ := cartierPullback_critical_residual_erasure (K := K) j E hE B d C s hsC hmiss
  have hEsSum : (∑ k, Es k) = ∑ i ∈ s, E i := sncSelectedPoints_cartier_sum E s
  change (Scheme.Modules.pullback j).obj (B - d • ∑ k, Es k).sheaf ≅ F.sheaf at aF
  rw [hEsSum] at aF
  let aR : (Scheme.Modules.pullback j).obj R.sheaf ≅ F.sheaf := aErase.symm ≪≫ aF
  obtain ⟨Q, aQ, aψ, hQgrades⟩ :=
    commuting_factorization_exists_center_adjoint_representative (j ≫ ρ) J.subschemeι ψ hψ D (d • KU + F) aD
  exact ⟨s, hs₀s, hs, hcrit, ℓ, rfl, U, hint, hclosed, E, hE, hI, hstrict, hRsupp, hRklt,
    (fun i hi his y => havoid (U.ι y) i (Finset.mem_filter.mp hi).2 his), cU, hintZ,
    ψ, hψ, hproper, hdom, hsurj, hover, hmap, F, Q, ⟨aR⟩, ⟨aD⟩, aQ, aψ, hDgrades, hQgrades⟩

end MixedFujita
