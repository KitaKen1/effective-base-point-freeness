/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentChosenIndependence

/-! 実選択SNC局所同型の任意affine制限一致。 check-296：元幾何のみから選択したSNC整成分の実局所標準層同型について、周囲・内部対象座標変更と全Cartier方程式変更からの独立性を証明。任意の対象エタール座標と独立な純正規化留数・frame単元でも同じ選択層同型を表すことを証明し、内部対象座標の選択が制限で一致するとの仮定を除去。元方程式の実affine制限チャートを構成し、選択済み実層写像の任意affine制限一致を空開を含む全部分開で証明。共通affine細分での両座標・全方程式比較と、一般点での一つの共通affine近傍・実線束の制限単射性から、任意二チャート重なりの全部分開で実写像の一致を証明。内部全点被覆と既存の加群層貼合せ・被覆上同型判定により、元j^*O(K_X+ΣE_i)とO(K_U)の一意な大域正規化随伴層同型を構成し、全部分開の局所写像との一致・各局所純留数と正確なframe単元による正規化を証明。最後に元smooth Noetherian SNC幾何の任意の交差点から、実整開閉成分・成分標準類参照チャート・同じ一意な大域随伴層同型まで内部供給する存在定理へ接続。全閉層・中間層の整性や、与えた成分・対象被覆・留数・局所同型・重なり証明・大域同型を追加仮定にしない。法線成分順序は固定。数値随伴・正値性・一般KV・F1F2は残る。 -/

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




/-- Actual affine restriction of original-data SNC component charts.
All restricted Cartier equations and SNC certificates are derived internally. -/
@[reducible]
noncomputable def sncComponentAdjunctionChartRestrict
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)

    (c : SNCComponentAdjunctionChart K (r := r) ξ E U)
    (W : X.affineOpens) [Nonempty W.1] (hWU : W.1 ≤ c.1.ambient.U)
    [Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ W.1)] :
    SNCComponentAdjunctionChart K (r := r) ξ E U := by
  let d : SNCAdjunctionChart K (r := r) ξ E :=
    { ambient := etaleChartAffineRestriction c.1.ambient W hWU
      selected := c.1.selected
      snc := isSNCChart_affineRestriction c.1.ambient c.1.snc W hWU
      equation := fun k => X.presheaf.map (homOfLE hWU).op (c.1.equation k)
      equation_ne_zero := fun k =>
        (regularEquation_restrict (E k) hWU (c.1.equation k)
          (c.1.equation_ne_zero k) (c.1.equation_spec k)).1
      equation_spec := fun k =>
        (regularEquation_restrict (E k) hWU (c.1.equation k)
          (c.1.equation_ne_zero k) (c.1.equation_spec k)).2
      cutNonempty := by
        change Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ W.1)
        infer_instance }
  exact ⟨d, fun _p hp => c.2 (hWU hp)⟩


/-- The CHOSEN normalized local SHEAF maps commute with every actual affine
restriction on ALL further subopens, including the empty open. Internal target
coordinates need not be compatible choices; pure-residue uniqueness removes them. -/
theorem sncComponentAdjunctionLocalIso_restrict
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
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U)
    (W : X.affineOpens) [Nonempty W.1] (hWU : W.1 ≤ c.1.ambient.U)
    [Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ W.1)] :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let i := U.ι ≫ I.subschemeι
    let Y : Scheme := U
    let M := (Scheme.Modules.pullback i).obj
      (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf
    let cW := sncComponentAdjunctionChartRestrict ξ E U c W hWU
    ∀ (Z : Y.Opens) (hZ : Z ≤ i ⁻¹ᵁ W.1) (s : Γ(M, Z)),
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ cW).hom.val.app
          (op (Over.mk (homOfLE hZ))) s =
        (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c).hom.val.app
          (op (Over.mk (homOfLE (hZ.trans (fun _x hx => hWU hx))))) s := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let i := U.ι ≫ I.subschemeι
  let Y : Scheme := U
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  letI : Nonempty (i ⁻¹ᵁ W.1) := by
    obtain ⟨p⟩ := (inferInstance : Nonempty (I.subschemeι ⁻¹ᵁ W.1))
    exact ⟨⟨⟨p.val, c.2 (hWU p.prop)⟩, p.prop⟩⟩
  let hY := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
  let KX := canonicalDivisor (m + r) cX₀ hX
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + ∑ k, E k).sheaf
  let cW := sncComponentAdjunctionChartRestrict ξ E U c W hWU
  let hpre : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ c.1.ambient.U := fun _x hx => hWU hx
  let cYC := etaleChartAffineRestriction (sncComponentAdjunctionCutChart ξ E U hclosed c)
    ⟨i ⁻¹ᵁ W.1, W.2.preimage i⟩ hpre
  dsimp only
  obtain ⟨R, a, R', hR, ha, hR', ha', _hnat, hcompat⟩ :=
    snc_component_local_adjunction_affine_restriction ξ hsnc U hclosed E hE hI
      c.1.ambient c.1.selected c.1.snc c.2 c.1.equation c.1.equation_ne_zero
      c.1.equation_spec W hWU (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
      (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale cX₀ hX cY₀
  have h₁ := sncComponentAdjunctionLocalIso_unique ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c R a hR ha
  have h₂ := sncComponentAdjunctionLocalIso_target_coordinates ξ E U hclosed hsnc hE hI cX₀ hX cY₀ cW
    cYC.coords cYC.formallyEtale R'
    (Units.map (sectionOpenRestrictionAlgHom (K := K) hpre).toRingHom.toMonoidHom a) hR' ha'
  have hcYC : ({ (sncComponentAdjunctionCutChart ξ E U hclosed cW) with
      coords := cYC.coords, formallyEtale := cYC.formallyEtale } : EtaleChart K U r) = cYC := by rfl
  simp only [hcYC] at h₂
  have hfx := canonicalPlusCartierSumEquation_affine_restriction cX₀ c.1.ambient W hWU
    c.1.equation c.1.equation_ne_zero cW.1.equation_ne_zero
  have hfy := etaleChartAffineRestriction_canonical_equation cY₀
    (sncComponentAdjunctionCutChart ξ E U hclosed c) ⟨i ⁻¹ᵁ W.1, W.2.preimage i⟩ hpre
  let fX := etaleChartCanonicalEquation cX₀ c.1.ambient *
    ∏ k, regularEquationRationalUnit X c.1.ambient.U (c.1.equation k) (c.1.equation_ne_zero k)
  let hfX := canonicalPlusCartierSum_local_equation cX₀ hX c.1.ambient E c.1.equation
    c.1.equation_ne_zero c.1.equation_spec
  let fY := etaleChartCanonicalEquation cY₀ (sncComponentAdjunctionCutChart ξ E U hclosed c)
  let hfY := (canonicalDivisor_restrict cY₀ hY (sncComponentAdjunctionCutChart ξ E U hclosed c)).symm
  have hpull (f₁ f₂ : X.functionFieldˣ)
      (h₁ : rationalUnitClass X W.1 (Additive.ofMul f₁) = (KX + ∑ k, E k) |_ W.1)
      (h₂ : rationalUnitClass X W.1 (Additive.ofMul f₂) = (KX + ∑ k, E k) |_ W.1)
      (h : f₁ = f₂) :
      cartierPullbackLocalFrameIso (KX + ∑ k, E k) i W.1 f₁ h₁ =
        cartierPullbackLocalFrameIso (KX + ∑ k, E k) i W.1 f₂ h₂ := by
    cases h
    rfl
  have hopen (f₁ f₂ : Y.functionFieldˣ)
      (h₁ : rationalUnitClass Y (i ⁻¹ᵁ W.1) (Additive.ofMul f₁) = KY |_ (i ⁻¹ᵁ W.1))
      (h₂ : rationalUnitClass Y (i ⁻¹ᵁ W.1) (Additive.ofMul f₂) = KY |_ (i ⁻¹ᵁ W.1))
      (h : f₁ = f₂) :
      cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) f₁ h₁ =
        cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) f₂ h₂ := by
    cases h
    rfl
  have he : sncComponentAdjunctionSourceFrame ξ E U hclosed cX₀ hX cW =
      moduleRestrictFrameOverIso M (i ⁻¹ᵁ W.1)
        (cartierPullbackLocalFrameIso (KX + ∑ k, E k) i W.1 fX
          (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX)) := by
    exact congrArg (moduleRestrictFrameOverIso M (i ⁻¹ᵁ W.1))
      (hpull _ _ (canonicalPlusCartierSum_local_equation cX₀ hX cW.1.ambient E cW.1.equation
        cW.1.equation_ne_zero cW.1.equation_spec)
          (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX) hfx)
  have hd : cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) (etaleChartCanonicalEquation cY₀ cYC)
        (canonicalDivisor_restrict cY₀ hY cYC).symm =
      cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) fY
        (CartierDivisor.rationalUnitClass_eq_of_le hpre hfY) := by
    exact hopen _ _ (canonicalDivisor_restrict cY₀ hY cYC).symm
      (CartierDivisor.rationalUnitClass_eq_of_le hpre hfY) hfy
  have h₂' := h₂
  change sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ cW =
    moduleOverFrameWeightedIso M KY.sheaf (i ⁻¹ᵁ W.1)
      (sncComponentAdjunctionSourceFrame ξ E U hclosed cX₀ hX cW)
      (cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) (etaleChartCanonicalEquation cY₀ cYC)
        (canonicalDivisor_restrict cY₀ hY cYC).symm)
      (Units.map (sectionOpenRestrictionAlgHom (K := K) hpre).toRingHom.toMonoidHom a) at h₂'
  rw [he, hd] at h₂'
  intro Z hZ s
  rw [h₁, h₂']
  exact hcompat Z hZ s

end MixedFujita
