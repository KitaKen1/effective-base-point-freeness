/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentAdjunctionNumericalIdentity
public import MixedFujita.CrepantBoundaryPerturbation

/-! 元crepant分子の実残余Cartier随伴・全倍数表示と次数恒等式。 check-297：実加群層引き戻しのCartier表示から任意の非優越な曲線合成射でも正確な次数一致を証明。元空間のample類から二つの十分大きい大域生成捻り・非零切断を内部構成し、元Cartier因子自身の非零切断を仮定せず、実Cartier引き戻しと実加群層引き戻しの同型を供給。296の実大域SNC随伴から、成分へ写る全ての実smooth proper曲線で標準類の次数恒等式を導き、任意の周囲随伴分子の残余引き戻しを一つの実Cartier因子Fで内部表示し、同じ標準類・Fによる全自然数倍の実層同型を供給。元のcrepant境界と引き戻し最高次形式の主因子補正を実線束同型として消去してからSNC成分へ制限し、元分子Dの実合成引き戻しがdK_U+Fとなることと全自然数倍の同じ表示を証明。有理形式係数の成分上での非消失を仮定しない。任意の実曲線について元Dの引き戻し次数がd倍のK_U次数と実残余B-dΣE_iの引き戻し次数の和に一致する厳密公式を証明。元のSNC素成分・単射性・余高さ1・臨界係数dから、実E_i・係数1辞書・残余の全臨界係数0・他素点での元係数保存を内部構成。元の分離的smooth Noetherianモデル上の任意交差点から、これらE_i・実整開閉成分・標準類参照チャート・同じ残余Fと元Dの全倍数層同型まで一括供給する存在定理へ接続。残余の正値性・中心への相対標準類比較・数値随伴・一般KV・F1F2は残る。 -/

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


/-- The original adjoint module pullback equals the actual crepant canonical
plus boundary numerator. The principal top-form correction is removed as an
actual line-bundle iso before any possibly nondominant restriction. -/
theorem crepant_adjoint_sheaf_iso_of_ample
    {K : Type u} [Field K] {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X]
    [V.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    {n : ℕ} [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (ρ : X ⟶ V) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cV : EtaleChart K V n) (f : V.functionFieldˣ) (cX : EtaleChart K X n)
    (H D : CartierDivisor V) (hH : CartierIsAmpleProj K H) (d : ℕ) :
    Nonempty ((Scheme.Modules.pullback ρ).obj D.sheaf ≅
      (d • smoothCanonicalDivisor cX + crepantBoundaryCartier ρ hρ cV f d D cX etaleCharts_cover).sheaf) := by
  let A := d • smoothCanonicalDivisor cX + crepantBoundaryCartier ρ hρ cV f d D cX etaleCharts_cover
  let u := crepantPullbackFormUnit ρ hρ cV f cX
  have hlin : cartierPullback ρ D = A + principalCartierDivisor X (u ^ d) := by
    rw [← crepantBoundaryCartier_smooth_recombine ρ hρ cV f d D cX,
      nsmul_add, principalCartierDivisor_power]
    dsimp only [A, u]
    abel
  obtain ⟨a⟩ := cartierPullback_sheaf_iso_modulePullback_of_ample H D hH ρ
  exact ⟨a ≪≫ eqToIso (congrArg CartierDivisor.sheaf hlin) ≪≫ cartierSheafPrincipalShiftIso A (u ^ d)⟩


/-- Original crepant geometry and GLOBAL SNC adjunction internally supply ONE
actual residual Cartier class on the component and the original adjoint
restriction in ALL degrees. No residual representation or restriction of a
rational top-form unit is input. -/
theorem crepant_snc_component_adjoint_restriction_representation
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
    {V : Scheme.{u}} [IsIntegral V] [V.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension (m + r) (X ↘ Spec (CommRingCat.of K))]
    (ρ : X ⟶ V) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cV : EtaleChart K V (m + r)) (f : V.functionFieldˣ)
    (H D : CartierDivisor V) (hH : CartierIsAmpleProj K H) (d : ℕ) :
    let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
    let B := crepantBoundaryCartier ρ hρ cV f d D cX₀ etaleCharts_cover
    let KU := canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
    ∃ F : CartierDivisor U,
      Nonempty ((Scheme.Modules.pullback j).obj (B - d • ∑ k, E k).sheaf ≅ F.sheaf) ∧
      Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj D.sheaf ≅ (d • KU + F).sheaf) ∧
      ∀ q : ℕ, Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj (q • D).sheaf ≅
        (q • (d • KU + F)).sheaf) := by
  let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
  let B := crepantBoundaryCartier ρ hρ cV f d D cX₀ etaleCharts_cover
  let KX := canonicalDivisor (m + r) cX₀ hX
  let KU := canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
  let A := d • KX + B
  obtain ⟨F, ⟨aF⟩, ⟨aA⟩, _hgrades⟩ :=
    snc_component_adjoint_restriction_representation ξ E U hclosed hsnc hE hI cX₀ hX cY₀ A d
  have hR : A - d • (KX + ∑ k, E k) = B - d • ∑ k, E k := by dsimp only [A]; rw [nsmul_add]; abel
  let aR : (Scheme.Modules.pullback j).obj (B - d • ∑ k, E k).sheaf ≅ F.sheaf :=
    (Scheme.Modules.pullback j).mapIso (eqToIso (congrArg CartierDivisor.sheaf hR.symm)) ≪≫ aF
  obtain ⟨aρ⟩ := crepant_adjoint_sheaf_iso_of_ample ρ hρ cV f cX₀ H D hH d
  let aD : (Scheme.Modules.pullback (j ≫ ρ)).obj D.sheaf ≅ (d • KU + F).sheaf :=
    (Scheme.Modules.pullbackComp j ρ).symm.app D.sheaf ≪≫
      (Scheme.Modules.pullback j).mapIso aρ ≪≫ aA
  exact ⟨F, ⟨aR⟩, ⟨aD⟩, fun q => ⟨cartierPullbackGradedIso D (j ≫ ρ) (d • KU + F) aD q⟩⟩


/-- Exact original-numerator degree formula along EVERY actual smooth proper
curve in the SNC component. The residual has no supplied sign; numerical
subadjunction still requires controlling this actual residual/fibration. -/
theorem crepant_snc_component_curve_adjoint_degree_identity
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
    {V : Scheme.{u}} [IsIntegral V] [V.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension (m + r) (X ↘ Spec (CommRingCat.of K))]
    (ρ : X ⟶ V) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cV : EtaleChart K V (m + r)) (f : V.functionFieldˣ)
    (H D : CartierDivisor V) (hH : CartierIsAmpleProj K H) (d : ℕ)
    {C : Scheme.{u}} [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hC : topologicalKrullDim C = 1) (φ : C ⟶ U) :
    let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
    let B := crepantBoundaryCartier ρ hρ cV f d D cX₀ etaleCharts_cover
    let KU := canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
    cartierCurvePullbackDegree (K := K) D (φ ≫ j ≫ ρ) =
      (d : ℤ) * cartierCurvePullbackDegree (K := K) KU φ +
        cartierCurvePullbackDegree (K := K) (B - d • ∑ k, E k) (φ ≫ j) := by
  let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
  let B := crepantBoundaryCartier ρ hρ cV f d D cX₀ etaleCharts_cover
  let KX := canonicalDivisor (m + r) cX₀ hX
  let A := d • KX + B
  obtain ⟨aρ⟩ := crepant_adjoint_sheaf_iso_of_ample ρ hρ cV f cX₀ H D hH d
  have hdegree := cartierCurvePullbackDegree_comp_of_representation (K := K) hC ρ (φ ≫ j) D A aρ
  have hR : A - d • (KX + ∑ k, E k) = B - d • ∑ k, E k := by dsimp only [A]; rw [nsmul_add]; abel
  have hs := snc_component_curve_adjoint_degree_identity ξ E U hclosed hsnc hE hI cX₀ hX cY₀ A d hC φ
  change cartierCurvePullbackDegree (K := K) A (φ ≫ j) =
    (d : ℤ) * cartierCurvePullbackDegree (K := K)
      (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)) φ +
        cartierCurvePullbackDegree (K := K) (A - d • (KX + ∑ k, E k)) (φ ≫ j) at hs
  rw [hR] at hs
  dsimp only
  rw [← Category.assoc]
  exact hdegree.trans hs

end MixedFujita
