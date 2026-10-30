/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineEtaleChartRestrictions

/-! 実Cartier frameと実pullback frameの全部分開制限一致。 check-285：恒等スキーム射の既存etale_appLEから任意のaffine開制限の形式的etale性を証明し、特定の局所化表示を入力せず実etaleチャートを任意の非空affine部分開へ構成。実一般点座標・微分基底・元の標準Cartier方程式が厳密に不変であることを証明。同じ有理方程式の実Cartier frameを元の開から制限したものと小さい開で作ったものが空開を含む全部分開で一致することを証明。実pullback済みframe生成元と切断pullbackの制限自然性から、実Cartier pullback frameの全部分開の制限一致も内部構成。純dg正規化による写像検出を任意のB加群へ拡張し、独立に構成した純正規化留数が任意の可換な実環図式で実引き戻し標準加群のチャート変更と可換であることを証明。実Cartier局所層同型への全環図式の接続、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
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


/-- An actual Cartier frame with the SAME rational equation agrees with its
restricted frame on EVERY further subopen, including the empty one. -/
theorem cartierOpenFrameCoefficient_affine_restriction
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)
    (U V : X.Opens) [Nonempty U] [Nonempty V] (hVU : V ≤ U)
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (W : X.Opens) (hWV : W ≤ V) (s : Γ(D.sheaf, W)) :
    moduleOverFrameCoefficient D.sheaf V
        (cartierOpenFrameIso D V f (CartierDivisor.rationalUnitClass_eq_of_le hVU hf)) W hWV s =
      moduleOverFrameCoefficient D.sheaf U (cartierOpenFrameIso D U f hf) W (hWV.trans hVU) s := by
  let e := moduleOverFrameRestrictIso D.sheaf U (cartierOpenFrameIso D U f hf) V hVU
  let d := cartierOpenFrameIso D V f (CartierDivisor.rationalUnitClass_eq_of_le hVU hf)
  have ht : ∀ t : Γ(D.sheaf, V),
      moduleOverFrameCoefficient D.sheaf V d V le_rfl t =
        (1 : Γ(X, V)) * moduleOverFrameCoefficient D.sheaf V e V le_rfl t := by
    intro t
    rw [one_mul]
    apply X.germToFunctionField_injective V
    change X.germToFunctionField V (cartierOpenCoefficient D V f (CartierDivisor.rationalUnitClass_eq_of_le hVU hf) V le_rfl t) =
      X.germToFunctionField V (cartierOpenCoefficient D U f hf V hVU t)
    rw [cartierOpenCoefficient_image, cartierOpenCoefficient_image]
  have h := moduleOverFrame_coefficient_change_of_top D.sheaf V e d 1 ht W hWV s
  simpa only [e, d, map_one, one_mul, moduleOverFrameRestrictIso_coefficient] using h


/-- Compatible original frames on nested opens give compatible ACTUAL
pullback frames on all subopens, via the pulled original generator. -/
theorem modulePulledOpenFrame_affine_restriction
    {X Y : Scheme.{u}} (i : Y ⟶ X) (M : X.Modules) (U V : X.Opens) (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (d : M.restrict V.ι ≅ SheafOfModules.unit (V : Scheme).ringCatSheaf)
    (he : ∀ t : Γ(M, V),
      moduleOverFrameCoefficient M V (moduleRestrictFrameOverIso M V d) V le_rfl t =
        moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) V hVU t)
    (W : Y.Opens) (hWV : W ≤ i ⁻¹ᵁ V) (s : Γ((Scheme.Modules.pullback i).obj M, W)) :
    moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj M) (i ⁻¹ᵁ V)
        (modulePulledOpenFrame i M V d) W hWV s =
      moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj M) (i ⁻¹ᵁ U)
        (modulePulledOpenFrame i M U e) W
          (hWV.trans (fun _x hx => hVU hx)) s := by
  let P := (Scheme.Modules.pullback i).obj M
  let t := moduleOpenFrameGenerator M U e
  let tV := M.presheaf.map (homOfLE hVU).op t
  let tY := modulePullbackSections i M V tV
  let hpre : i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U := fun _x hx => hVU hx
  let a := moduleOverFrameRestrictIso P (i ⁻¹ᵁ U) (modulePulledOpenFrame i M U e) (i ⁻¹ᵁ V) hpre
  have hres : tY = P.presheaf.map (homOfLE hpre).op (modulePullbackSections i M U t) :=
    modulePullbackSections_restrict i M (homOfLE hVU) t
  have htV : moduleOverFrameCoefficient M U (moduleRestrictFrameOverIso M U e) V hVU tV = 1 := by
    rw [moduleOverFrameCoefficient_restrict _ _ _ le_rfl,
      moduleOpenFrameGenerator_coefficient, map_one]
  have hdY : moduleOverFrameCoefficient P (i ⁻¹ᵁ V) (modulePulledOpenFrame i M V d)
      (i ⁻¹ᵁ V) le_rfl tY = 1 := by
    rw [modulePulledOpenFrame, modulePullbackSections_local_frame_coefficient, he, htV, map_one]
  have haY : moduleOverFrameCoefficient P (i ⁻¹ᵁ V) a (i ⁻¹ᵁ V) le_rfl tY = 1 := by
    change moduleOverFrameCoefficient P (i ⁻¹ᵁ U) (modulePulledOpenFrame i M U e)
      (i ⁻¹ᵁ V) hpre tY = 1
    rw [hres, moduleOverFrameCoefficient_restrict _ _ _ le_rfl,
      modulePullbackFrameGenerator_coefficient, map_one]
  conv_lhs => rw [moduleFrame_section_eq_coefficient_smul P (i ⁻¹ᵁ V) a tY haY W hWV s]
  rw [map_smul, moduleOverFrameCoefficient_restrict _ _ _ le_rfl,
    hdY, map_one, smul_eq_mul, mul_one]
  rfl


/-- Restricting an actual Cartier equation frame commutes with ACTUAL
module pullback on every subopen, including empty opens. No frame comparison
certificate or rational function pullback along the immersion is input. -/
theorem cartierPullbackFrameCoefficient_affine_restriction
    {X Y : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (i : Y ⟶ X)
    (U V : X.Opens) [Nonempty U] [Nonempty V] (hVU : V ≤ U)
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (W : Y.Opens) (hWV : W ≤ i ⁻¹ᵁ V) (s : Γ((Scheme.Modules.pullback i).obj D.sheaf, W)) :
    moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj D.sheaf) (i ⁻¹ᵁ V)
        (moduleRestrictFrameOverIso _ _ (cartierPullbackLocalFrameIso D i V f
          (CartierDivisor.rationalUnitClass_eq_of_le hVU hf))) W hWV s =
      moduleOverFrameCoefficient ((Scheme.Modules.pullback i).obj D.sheaf) (i ⁻¹ᵁ U)
        (moduleRestrictFrameOverIso _ _ (cartierPullbackLocalFrameIso D i U f hf)) W
          (hWV.trans (fun _x hx => hVU hx)) s := by
  apply modulePulledOpenFrame_affine_restriction i D.sheaf U V hVU
    (cartierOpenRestrictFrameIso D U f hf)
    (cartierOpenRestrictFrameIso D V f (CartierDivisor.rationalUnitClass_eq_of_le hVU hf))
  intro t
  dsimp only [cartierOpenRestrictFrameIso]
  rw [moduleRestrictFrameOverIso_roundTrip, moduleRestrictFrameOverIso_roundTrip]
  exact cartierOpenFrameCoefficient_affine_restriction D U V hVU f hf V le_rfl t

end MixedFujita
