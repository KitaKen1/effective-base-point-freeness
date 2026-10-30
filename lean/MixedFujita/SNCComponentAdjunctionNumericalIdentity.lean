/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPullbackDegreeComparison

/-! SNC実大域随伴の全曲線次数恒等式と同じ残余類の全倍数表示。 check-297：実加群層引き戻しのCartier表示から任意の非優越な曲線合成射でも正確な次数一致を証明。元空間のample類から二つの十分大きい大域生成捻り・非零切断を内部構成し、元Cartier因子自身の非零切断を仮定せず、実Cartier引き戻しと実加群層引き戻しの同型を供給。296の実大域SNC随伴から、成分へ写る全ての実smooth proper曲線で標準類の次数恒等式を導き、任意の周囲随伴分子の残余引き戻しを一つの実Cartier因子Fで内部表示し、同じ標準類・Fによる全自然数倍の実層同型を供給。元のcrepant境界と引き戻し最高次形式の主因子補正を実線束同型として消去してからSNC成分へ制限し、元分子Dの実合成引き戻しがdK_U+Fとなることと全自然数倍の同じ表示を証明。有理形式係数の成分上での非消失を仮定しない。任意の実曲線について元Dの引き戻し次数がd倍のK_U次数と実残余B-dΣE_iの引き戻し次数の和に一致する厳密公式を証明。元のSNC素成分・単射性・余高さ1・臨界係数dから、実E_i・係数1辞書・残余の全臨界係数0・他素点での元係数保存を内部構成。元の分離的smooth Noetherianモデル上の任意交差点から、これらE_i・実整開閉成分・標準類参照チャート・同じ残余Fと元Dの全倍数層同型まで一括供給する存在定理へ接続。残余の正値性・中心への相対標準類比較・数値随伴・一般KV・F1F2は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra




attribute [local instance] Classical.propDecidable


/-- The GLOBAL actual SNC adjunction gives an exact degree identity on
EVERY actual smooth proper curve mapping to the component. -/
theorem snc_component_adjunction_curve_degree
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r)
    {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hC : topologicalKrullDim C = 1) (φ : C ⟶ U) :
    cartierCurvePullbackDegree (K := K) (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k)
        (φ ≫ U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) =
      cartierCurvePullbackDegree (K := K)
        (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)) φ := by
  exact cartierCurvePullbackDegree_comp_of_representation hC _ φ _ _
    (sncComponentGlobalAdjunctionIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀)


/-- Any ambient adjoint numerator has an actual residual Cartier representative
on the SNC component; the SAME representative and canonical class work for
ALL further multiples. The residual line bundle is supplied internally. -/
theorem snc_component_adjoint_restriction_representation
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r)
    (A : CartierDivisor X) (d : ℕ) :
    let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
    let KX := canonicalDivisor (m + r) cX₀ hX
    let KU := canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
    let R := A - d • (KX + ∑ k, E k)
    ∃ F : CartierDivisor U,
      Nonempty ((Scheme.Modules.pullback j).obj R.sheaf ≅ F.sheaf) ∧
      Nonempty ((Scheme.Modules.pullback j).obj A.sheaf ≅ (d • KU + F).sheaf) ∧
      ∀ q : ℕ, Nonempty ((Scheme.Modules.pullback j).obj (q • A).sheaf ≅ (q • (d • KU + F)).sheaf) := by
  let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
  let KX := canonicalDivisor (m + r) cX₀ hX
  let KU := canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
  let R := A - d • (KX + ∑ k, E k)
  obtain ⟨F, ⟨aF⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor R j
  let aK := sncComponentGlobalAdjunctionIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀
  have hA : A = d • (KX + ∑ k, E k) + R := by dsimp only [R]; abel
  let aA : (Scheme.Modules.pullback j).obj A.sheaf ≅ (d • KU + F).sheaf :=
    (Scheme.Modules.pullback j).mapIso (eqToIso (congrArg CartierDivisor.sheaf hA)) ≪≫
      (Scheme.Modules.pullback j).mapIso (cartierTensorSheafIso (d • (KX + ∑ k, E k)) R).symm ≪≫
        cartierPullbackTensorIso (d • (KX + ∑ k, E k)) j R.sheaf ≪≫
          MonoidalCategory.tensorIso (cartierPullbackGradedIso (KX + ∑ k, E k) j KU aK d) aF ≪≫
            cartierTensorSheafIso (d • KU) F
  exact ⟨F, ⟨aF⟩, ⟨aA⟩, fun q => ⟨cartierPullbackGradedIso A j (d • KU + F) aA q⟩⟩


/-- Exact adjoint degree formula: the remaining numerical subadjunction gap
is precisely the degree of the ACTUAL ambient residual on the same curve. -/
theorem snc_component_curve_adjoint_degree_identity
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (hsnc : IsSNCFamily K (m + r) ξ) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r)
    (A : CartierDivisor X) (d : ℕ)
    {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hC : topologicalKrullDim C = 1) (φ : C ⟶ U) :
    let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
    let KX := canonicalDivisor (m + r) cX₀ hX
    let KU := canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
    cartierCurvePullbackDegree (K := K) A (φ ≫ j) =
      (d : ℤ) * cartierCurvePullbackDegree (K := K) KU φ +
        cartierCurvePullbackDegree (K := K) (A - d • (KX + ∑ k, E k)) (φ ≫ j) := by
  let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
  let KX := canonicalDivisor (m + r) cX₀ hX
  let R := A - d • (KX + ∑ k, E k)
  have hA : A = d • (KX + ∑ k, E k) + R := by dsimp only [R]; abel
  have heq := congrArg (cartierCurvePullbackDegreeHom (K := K) hC (φ ≫ j)) hA
  rw [map_add, map_nsmul, nsmul_eq_mul] at heq
  change cartierCurvePullbackDegree (K := K) A (φ ≫ j) =
    (d : ℤ) * cartierCurvePullbackDegree (K := K) (KX + ∑ k, E k) (φ ≫ j) +
      cartierCurvePullbackDegree (K := K) R (φ ≫ j) at heq
  rw [snc_component_adjunction_curve_degree ξ E U hclosed hsnc hE hI cX₀ hX cY₀ hC φ] at heq
  exact heq

end MixedFujita
