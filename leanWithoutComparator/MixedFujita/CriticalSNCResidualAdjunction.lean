/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CrepantSNCComponentAdjunction

/-! 元臨界SNC幾何から成分・係数消去・全倍数随伴表示を内部供給。 check-297：実加群層引き戻しのCartier表示から任意の非優越な曲線合成射でも正確な次数一致を証明。元空間のample類から二つの十分大きい大域生成捻り・非零切断を内部構成し、元Cartier因子自身の非零切断を仮定せず、実Cartier引き戻しと実加群層引き戻しの同型を供給。296の実大域SNC随伴から、成分へ写る全ての実smooth proper曲線で標準類の次数恒等式を導き、任意の周囲随伴分子の残余引き戻しを一つの実Cartier因子Fで内部表示し、同じ標準類・Fによる全自然数倍の実層同型を供給。元のcrepant境界と引き戻し最高次形式の主因子補正を実線束同型として消去してからSNC成分へ制限し、元分子Dの実合成引き戻しがdK_U+Fとなることと全自然数倍の同じ表示を証明。有理形式係数の成分上での非消失を仮定しない。任意の実曲線について元Dの引き戻し次数がd倍のK_U次数と実残余B-dΣE_iの引き戻し次数の和に一致する厳密公式を証明。元のSNC素成分・単射性・余高さ1・臨界係数dから、実E_i・係数1辞書・残余の全臨界係数0・他素点での元係数保存を内部構成。元の分離的smooth Noetherianモデル上の任意交差点から、これらE_i・実整開閉成分・標準類参照チャート・同じ残余Fと元Dの全倍数層同型まで一括供給する存在定理へ接続。残余の正値性・中心への相対標準類比較・数値随伴・一般KV・F1F2は残る。 -/

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


/-- ORIGINAL SNC prime geometry constructs actual coefficient-one Cartier
components and deletes exactly the critical coefficients from a numerator.
The residual coefficients elsewhere are preserved. No component divisors or
coefficient dictionary is supplied. -/
theorem exists_snc_critical_residual_components
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    {n m : ℕ} (ξ : Fin m → X) (hinj : Function.Injective ξ)
    (hξ : ∀ k, Order.coheight (ξ k) = 1) (hsnc : IsSNCFamily K n ξ)
    (B : CartierDivisor X) (d : ℕ) (hcrit : ∀ k, cartierCoefficient B (ξ k) = (d : ℤ)) :
    ∃ (E : Fin m → CartierDivisor X) (hE : ∀ k, (E k).IsEffective)
      (_hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X)),
      (∀ (k : Fin m) (z : TauCeti.AlgebraicGeometry.CodimensionOnePoint X),
        cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0) ∧
      (∀ k, cartierCoefficient (B - d • ∑ i, E i) (ξ k) = 0) ∧
      ∀ z : TauCeti.AlgebraicGeometry.CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
        cartierCoefficient (B - d • ∑ i, E i) (z : X) = cartierCoefficient B (z : X) := by
  classical
  obtain ⟨E, hE, hI, hEc⟩ := exists_snc_component_cartier ξ hξ hsnc
  refine ⟨E, hE, hI, hEc, ?_, ?_⟩
  · intro k
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, cartierCoefficient_sum, hcrit]
    have hsum : ∑ i, cartierCoefficient (E i) (ξ k) = 1 := by
      simp only [hEc _ ⟨ξ k, hξ k⟩]
      have heq (i : Fin m) : ξ k = ξ i ↔ k = i := ⟨fun h => hinj h, fun h => congrArg ξ h⟩
      simp only [heq]
      simp
    rw [hsum, mul_one, sub_self]
  · intro z hz
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, cartierCoefficient_sum]
    have hzero (i : Fin m) : cartierCoefficient (E i) (z : X) = 0 := by
      rw [hEc i z, ite_eq_right (fun h => hz ⟨i, h.symm⟩)]
    simp only [hzero, Finset.sum_const_zero, mul_zero, sub_zero]


/-- From ORIGINAL crepant/SNC critical data and an actual stratum point,
construct the component divisors, exact critical residual, actual integral
clopen component and its canonical reference, then ONE residual Cartier class
and the original adjoint restriction for ALL natural multiples. -/
theorem crepant_snc_original_geometry_exists_component_adjoint_restriction_at
    {K : Type u} [Field K] {V X : Scheme.{u}} [IsIntegral V] [IsIntegral X] [IsNoetherian X]
    [V.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} [SmoothOfRelativeDimension (m + r) (X ↘ Spec (CommRingCat.of K))]
    (ρ : X ⟶ V) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cV : EtaleChart K V (m + r)) (f : V.functionFieldˣ) (cX : EtaleChart K X (m + r))
    (H D : CartierDivisor V) (hH : CartierIsAmpleProj K H) (d : ℕ)
    (ξ : Fin m → X) (hinj : Function.Injective ξ) (hξ : ∀ k, Order.coheight (ξ k) = 1)
    (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (hcrit : ∀ k, cartierCoefficient (crepantBoundaryCartier ρ hρ cV f d D cX etaleCharts_cover) (ξ k) = (d : ℤ))
    (p : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) :
    let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (m + r) _
    let B := crepantBoundaryCartier ρ hρ cV f d D cX etaleCharts_cover
    ∃ (E : Fin m → CartierDivisor X) (hE : ∀ k, (E k).IsEffective)
      (_hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X)),
      (∀ (k : Fin m) (z : TauCeti.AlgebraicGeometry.CodimensionOnePoint X),
        cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0) ∧
      (∀ k, cartierCoefficient (B - d • ∑ i, E i) (ξ k) = 0) ∧
      (∀ z : TauCeti.AlgebraicGeometry.CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
        cartierCoefficient (B - d • ∑ i, E i) (z : X) = cartierCoefficient B (z : X)) ∧
      ∃ (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
        (hint : IsIntegral U)
        (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
        (_hp : p ∈ U) (cU : EtaleChart K U r),
        let : IsIntegral U := hint
        let j := U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι
        let KU := canonicalDivisor r cU (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
        ∃ F : CartierDivisor U,
          Nonempty ((Scheme.Modules.pullback j).obj (B - d • ∑ k, E k).sheaf ≅ F.sheaf) ∧
          Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj D.sheaf ≅ (d • KU + F).sheaf) ∧
          ∀ q : ℕ, Nonempty ((Scheme.Modules.pullback (j ≫ ρ)).obj (q • D).sheaf ≅
            (q • (d • KU + F)).sheaf) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (m + r) _
  let B := crepantBoundaryCartier ρ hρ cV f d D cX etaleCharts_cover
  obtain ⟨E, hE, hI, hEc, hzero, houtside⟩ :=
    exists_snc_critical_residual_components ξ hinj hξ hsnc B d hcrit
  obtain ⟨U, _W, hpU, _hpW, _hWU, hclosed, hint, _hj⟩ :=
    snc_stratum_exists_lifted_integral_component ξ hsnc p
  let : IsIntegral U := hint
  have hcover := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
  have hgeneric : genericPoint U ∈ iSup (fun c : EtaleChart K U r => c.U) := by
    rw [hcover]
    trivial
  obtain ⟨cU, _hcU⟩ := Opens.mem_iSup.mp hgeneric
  exact ⟨E, hE, hI, hEc, hzero, houtside, U, hint, hclosed, hpU, cU,
    crepant_snc_component_adjoint_restriction_representation ξ E U hclosed hsnc hE hI
      cX etaleCharts_cover cU ρ hρ cV f H D hH d⟩

end MixedFujita
