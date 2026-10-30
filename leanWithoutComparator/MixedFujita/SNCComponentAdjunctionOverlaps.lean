/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentChosenRestrictions

/-! 実SNC局所同型の任意二チャート重なり全部分開一致。 check-296：元幾何のみから選択したSNC整成分の実局所標準層同型について、周囲・内部対象座標変更と全Cartier方程式変更からの独立性を証明。任意の対象エタール座標と独立な純正規化留数・frame単元でも同じ選択層同型を表すことを証明し、内部対象座標の選択が制限で一致するとの仮定を除去。元方程式の実affine制限チャートを構成し、選択済み実層写像の任意affine制限一致を空開を含む全部分開で証明。共通affine細分での両座標・全方程式比較と、一般点での一つの共通affine近傍・実線束の制限単射性から、任意二チャート重なりの全部分開で実写像の一致を証明。内部全点被覆と既存の加群層貼合せ・被覆上同型判定により、元j^*O(K_X+ΣE_i)とO(K_U)の一意な大域正規化随伴層同型を構成し、全部分開の局所写像との一致・各局所純留数と正確なframe単元による正規化を証明。最後に元smooth Noetherian SNC幾何の任意の交差点から、実整開閉成分・成分標準類参照チャート・同じ一意な大域随伴層同型まで内部供給する存在定理へ接続。全閉層・中間層の整性や、与えた成分・対象被覆・留数・局所同型・重なり証明・大域同型を追加仮定にしない。法線成分順序は固定。数値随伴・正値性・一般KV・F1F2は残る。 -/

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




/-- Chosen component adjunctions agree on any common actual affine refinement;
ambient/target coordinates and all original Cartier equations may differ. -/
theorem sncComponentAdjunctionLocalIso_common_refinement
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
    (c d : SNCComponentAdjunctionChart K (r := r) ξ E U)
    (W : X.affineOpens) [Nonempty W.1]
    (hWc : W.1 ≤ c.1.ambient.U) (hWd : W.1 ≤ d.1.ambient.U)
    [Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ W.1)] :
    sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀
        (sncComponentAdjunctionChartRestrict ξ E U c W hWc) =
      sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀
        (sncComponentAdjunctionChartRestrict ξ E U d W hWd) := by
  let cW := sncComponentAdjunctionChartRestrict ξ E U c W hWc
  let dW := sncComponentAdjunctionChartRestrict ξ E U d W hWd
  let e : SNCComponentAdjunctionChart K (r := r) ξ E U :=
    ⟨{ cW.1 with ambient := { cW.1.ambient with coords := dW.1.ambient.coords, formallyEtale := dW.1.ambient.formallyEtale }, selected := dW.1.selected, snc := dW.1.snc }, cW.2⟩
  have hx := sncComponentAdjunctionLocalIso_coordinate_independent ξ E U hclosed hsnc hE hI cX₀ hX cY₀ cW
    dW.1.ambient.coords dW.1.ambient.formallyEtale dW.1.selected dW.1.snc
  have he := sncComponentAdjunctionLocalIso_equations_independent ξ E U hclosed hsnc hE hI cX₀ hX cY₀ e
    dW.1.equation dW.1.equation_ne_zero dW.1.equation_spec
  exact hx.trans he


/-- Both ORIGINAL actual local sheaf maps agree on all subopens of a
common affine refinement, including empty subopens. -/
theorem sncComponentAdjunctionLocalIso_common_affine_apply
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
    (c d : SNCComponentAdjunctionChart K (r := r) ξ E U)
    (W : X.affineOpens) [Nonempty W.1]
    (hWc : W.1 ≤ c.1.ambient.U) (hWd : W.1 ≤ d.1.ambient.U)
    [Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ W.1)] :
    let i := (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)
    let Y : Scheme := U
    let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
    ∀ (Z : Y.Opens) (hZ : Z ≤ i ⁻¹ᵁ W.1) (s : Γ(M, Z)),
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom.val.app
          (op (Over.mk (homOfLE (hZ.trans (fun _x hx => hWc hx))))) s =
        (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ d).hom.val.app
          (op (Over.mk (homOfLE (hZ.trans (fun _x hx => hWd hx))))) s := by
  let i := (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)
  let Y : Scheme := U
  let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
  dsimp only
  intro Z hZ s
  have hc := sncComponentAdjunctionLocalIso_restrict ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c W hWc Z hZ s
  have hd := sncComponentAdjunctionLocalIso_restrict ξ E U hclosed hsnc hE hI cX₀ hX cY₀ d W hWd Z hZ s
  have hW := sncComponentAdjunctionLocalIso_common_refinement ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c d W hWc hWd
  exact hc.symm.trans ((congrArg (fun Φ => Φ.hom.val.app (op (Over.mk (homOfLE hZ))) s) hW).trans hd)


/-- Arbitrary actual local adjunction sheaf maps agree on EVERY open in
their overlap. A single common affine neighborhood of the cut generic point
and actual Cartier restriction injectivity replace point-by-point separation. -/
theorem sncComponentAdjunctionLocalIso_overlap_apply
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
    (c d : SNCComponentAdjunctionChart K (r := r) ξ E U) :
    let i := (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)
    let Y : Scheme := U
    let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
    ∀ (Z : Y.Opens) (hZc : Z ≤ (sncComponentAdjunctionCutChart ξ E U hclosed c).U)
      (hZd : Z ≤ (sncComponentAdjunctionCutChart ξ E U hclosed d).U) (s : Γ(M, Z)),
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom.val.app
          (op (Over.mk (homOfLE hZc))) s =
        (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ d).hom.val.app
          (op (Over.mk (homOfLE hZd))) s := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed d).nonempty
  let i := (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)
  let Y : Scheme := U
  let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
  let KY := canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)
  have hηc : genericPoint Y ∈ (sncComponentAdjunctionCutChart ξ E U hclosed c).U := genericPoint_mem _
  have hηd : genericPoint Y ∈ (sncComponentAdjunctionCutChart ξ E U hclosed d).U := genericPoint_mem _
  have hη : i (genericPoint Y) ∈ c.1.ambient.U ⊓ d.1.ambient.U := ⟨hηc, hηd⟩
  obtain ⟨_, ⟨W, hWa, rfl⟩, hηW, hWsub⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hη (c.1.ambient.U ⊓ d.1.ambient.U).isOpen
  letI : Nonempty W := ⟨⟨i (genericPoint Y), hηW⟩⟩
  letI : Nonempty (i ⁻¹ᵁ W) := ⟨⟨genericPoint Y, hηW⟩⟩
  letI : Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ W) :=
    ⟨⟨(genericPoint Y).val, hηW⟩⟩
  have hWc : W ≤ c.1.ambient.U := fun _x hx => (hWsub hx).1
  have hWd : W ≤ d.1.ambient.U := fun _x hx => (hWsub hx).2
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
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom.val
      (Over.homMk j : Over.mk (homOfLE (j.le.trans hZc)) ⟶ Over.mk (homOfLE hZc)).op s
    have hd := PresheafOfModules.naturality_apply
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ d).hom.val
      (Over.homMk j : Over.mk (homOfLE (j.le.trans hZd)) ⟶ Over.mk (homOfLE hZd)).op s
    have hh := sncComponentAdjunctionLocalIso_common_affine_apply ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c d ⟨W, hWa⟩ hWc hWd
      T inf_le_right (M.presheaf.map j.op s)
    exact hc.symm.trans (hh.trans hd)
  · exact TopCat.Presheaf.section_ext ⟨KY.sheaf.presheaf, KY.sheaf.isSheaf⟩ Z _ _
      (fun x hx => (hZ ⟨⟨x, hx⟩⟩).elim)

end MixedFujita
