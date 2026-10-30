/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCartierAdjunctionRestrictions
public import TauCeti.AlgebraicGeometry.LineBundle.Germ

/-! 任意二Cartier随伴チャートの重なりの全部分開一致。 check-287：実周囲etale座標・実正則Cartier方程式・実切断座標だけを持つ局所チャートを定義し、既存の実局所標準随伴層同型を選ぶ。純正規化留数の一意性と最高次楔積の係数単射性から、独立構成した任意の正規化留数・frame単元でも同じ選択局所同型になることを証明。選択済み同型について周囲／切断の同時座標変更と正則方程式変更からの独立性、任意affine細分での全部分開制限一致を証明。共通affine細分における二同型の一致を導き、切断の一般点を含む一つの共通affine開とTauCetiの実線束制限の単射性から、任意二チャートの重なりの全ての部分開で元の実層写像が一致することを証明。空開も含む。全点を覆う局所チャートの存在の接続、大域留数層同型の貼合せ、SNC反復随伴、数値随伴は残る。 -/

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

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] {D : CartierDivisor X} {hD : D.IsEffective}
  [(effectiveCartierIdealSheaf D hD).subscheme.Over (Spec (CommRingCat.of K))]
  [(effectiveCartierIdealSheaf D hD).subschemeι.IsOver (Spec (CommRingCat.of K))]
  [IsIntegral (effectiveCartierIdealSheaf D hD).subscheme] {r : ℕ}



/-- Independently chosen local adjunctions agree on ANY common nonempty
affine refinement, after changing both coordinate systems and the actual equation. -/
theorem cartierAdjunctionLocalIso_common_refinement
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c d : CartierAdjunctionChart K D hD r)
    (W : X.affineOpens) [Nonempty W.1]
    (hWc : W.1 ≤ c.ambient.U) (hWd : W.1 ≤ d.ambient.U)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1)] :
    cartierAdjunctionLocalIso cX₀ hX cY₀ hY (cartierAdjunctionChartRestrict c W hWc) =
      cartierAdjunctionLocalIso cX₀ hX cY₀ hY (cartierAdjunctionChartRestrict d W hWd) := by
  let cW := cartierAdjunctionChartRestrict c W hWc
  let dW := cartierAdjunctionChartRestrict d W hWd
  let e : CartierAdjunctionChart K D hD r :=
    { cW with ambient := { cW.ambient with coords := dW.ambient.coords, formallyEtale := dW.ambient.formallyEtale }, cutCoords := dW.cutCoords, cutEtale := dW.cutEtale }
  have hx := cartierAdjunctionLocalIso_coordinate_independent cX₀ hX cY₀ hY cW
    dW.ambient.coords dW.ambient.formallyEtale dW.cutCoords dW.cutEtale
  have he := cartierAdjunctionLocalIso_equation_independent cX₀ hX cY₀ hY e
    dW.equation dW.equation_ne_zero dW.equation_spec
  exact hx.trans he


/-- Both ORIGINAL actual local sheaf maps agree on all subopens of a
common affine refinement, including empty subopens. -/
theorem cartierAdjunctionLocalIso_common_affine_apply
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c d : CartierAdjunctionChart K D hD r)
    (W : X.affineOpens) [Nonempty W.1]
    (hWc : W.1 ≤ c.ambient.U) (hWd : W.1 ≤ d.ambient.U)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1)] :
    let i := (effectiveCartierIdealSheaf D hD).subschemeι
    let Y := (effectiveCartierIdealSheaf D hD).subscheme
    let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
    ∀ (Z : Y.Opens) (hZ : Z ≤ i ⁻¹ᵁ W.1) (s : Γ(M, Z)),
      (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom.val.app
          (op (Over.mk (homOfLE (hZ.trans (fun _x hx => hWc hx))))) s =
        (cartierAdjunctionLocalIso cX₀ hX cY₀ hY d).hom.val.app
          (op (Over.mk (homOfLE (hZ.trans (fun _x hx => hWd hx))))) s := by
  let i := (effectiveCartierIdealSheaf D hD).subschemeι
  let Y := (effectiveCartierIdealSheaf D hD).subscheme
  let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
  dsimp only
  intro Z hZ s
  have hc := cartierAdjunctionLocalIso_restrict cX₀ hX cY₀ hY c W hWc Z hZ s
  have hd := cartierAdjunctionLocalIso_restrict cX₀ hX cY₀ hY d W hWd Z hZ s
  have hW := cartierAdjunctionLocalIso_common_refinement cX₀ hX cY₀ hY c d W hWc hWd
  exact hc.symm.trans ((congrArg (fun Φ => Φ.hom.val.app (op (Over.mk (homOfLE hZ))) s) hW).trans hd)


/-- Arbitrary actual local adjunction sheaf maps agree on EVERY open in
their overlap. A single common affine neighborhood of the cut generic point
and actual Cartier restriction injectivity replace point-by-point separation. -/
theorem cartierAdjunctionLocalIso_overlap_apply
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c d : CartierAdjunctionChart K D hD r) :
    let i := (effectiveCartierIdealSheaf D hD).subschemeι
    let Y := (effectiveCartierIdealSheaf D hD).subscheme
    let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
    ∀ (Z : Y.Opens) (hZc : Z ≤ (cartierAdjunctionCutChart c).U)
      (hZd : Z ≤ (cartierAdjunctionCutChart d).U) (s : Γ(M, Z)),
      (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom.val.app
          (op (Over.mk (homOfLE hZc))) s =
        (cartierAdjunctionLocalIso cX₀ hX cY₀ hY d).hom.val.app
          (op (Over.mk (homOfLE hZd))) s := by
  letI := c.cutNonempty
  letI := d.cutNonempty
  let i := (effectiveCartierIdealSheaf D hD).subschemeι
  let Y := (effectiveCartierIdealSheaf D hD).subscheme
  let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
  let KY := canonicalDivisor r cY₀ hY
  have hηc : genericPoint Y ∈ (cartierAdjunctionCutChart c).U := genericPoint_mem _
  have hηd : genericPoint Y ∈ (cartierAdjunctionCutChart d).U := genericPoint_mem _
  have hη : i (genericPoint Y) ∈ c.ambient.U ⊓ d.ambient.U := ⟨hηc, hηd⟩
  obtain ⟨_, ⟨W, hWa, rfl⟩, hηW, hWsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hη (c.ambient.U ⊓ d.ambient.U).isOpen
  letI : Nonempty W := ⟨⟨i (genericPoint Y), hηW⟩⟩
  letI : Nonempty (i ⁻¹ᵁ W) := ⟨⟨genericPoint Y, hηW⟩⟩
  have hWc : W ≤ c.ambient.U := fun _x hx => (hWsub hx).1
  have hWd : W ≤ d.ambient.U := fun _x hx => (hWsub hx).2
  dsimp only
  intro Z hZc hZd s
  by_cases hZ : Nonempty Z
  · letI := hZ
    let T : Y.Opens := Z ⊓ i ⁻¹ᵁ W
    letI : Nonempty T := ⟨⟨genericPoint Y, genericPoint_mem Z, hηW⟩⟩
    let j : T ⟶ Z := homOfLE inf_le_left
    apply TauCeti.AlgebraicGeometry.InvertibleSheaf.map_injective_of_isIntegral
      ⟨KY.sheaf, KY.isInvertible_sheaf⟩ j
    have hc := PresheafOfModules.naturality_apply
      (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom.val
      (Over.homMk j : Over.mk (homOfLE (j.le.trans hZc)) ⟶ Over.mk (homOfLE hZc)).op s
    have hd := PresheafOfModules.naturality_apply
      (cartierAdjunctionLocalIso cX₀ hX cY₀ hY d).hom.val
      (Over.homMk j : Over.mk (homOfLE (j.le.trans hZd)) ⟶ Over.mk (homOfLE hZd)).op s
    have hh := cartierAdjunctionLocalIso_common_affine_apply cX₀ hX cY₀ hY c d ⟨W, hWa⟩ hWc hWd
      T inf_le_right (M.presheaf.map j.op s)
    exact hc.symm.trans (hh.trans hd)
  · exact TopCat.Presheaf.section_ext ⟨KY.sheaf.presheaf, KY.sheaf.isSheaf⟩ Z _ _
      (fun x hx => (hZ ⟨⟨x, hx⟩⟩).elim)

end MixedFujita
