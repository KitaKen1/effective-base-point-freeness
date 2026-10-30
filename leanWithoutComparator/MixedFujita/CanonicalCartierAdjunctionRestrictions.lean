/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalCartierAdjunctionCharts

/-! 実選択局所随伴同型の座標・方程式独立性とaffine制限。 check-287：実周囲etale座標・実正則Cartier方程式・実切断座標だけを持つ局所チャートを定義し、既存の実局所標準随伴層同型を選ぶ。純正規化留数の一意性と最高次楔積の係数単射性から、独立構成した任意の正規化留数・frame単元でも同じ選択局所同型になることを証明。選択済み同型について周囲／切断の同時座標変更と正則方程式変更からの独立性、任意affine細分での全部分開制限一致を証明。共通affine細分における二同型の一致を導き、切断の一般点を含む一つの共通affine開とTauCetiの実線束制限の単射性から、任意二チャートの重なりの全ての部分開で元の実層写像が一致することを証明。空開も含む。全点を覆う局所チャートの存在の接続、大域留数層同型の貼合せ、SNC反復随伴、数値随伴は残る。 -/

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



/-- The chosen actual local adjunction is unchanged by simultaneous
ambient and cut etale coordinate changes on the same affine open. -/
theorem cartierAdjunctionLocalIso_coordinate_independent
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r)
    (x' : MvPolynomial (Fin (1 + r)) K →ₐ[K] Γ(X, c.ambient.U))
    (hx' : x'.toRingHom.FormallyEtale)
    (y' : MvPolynomial (Fin r) K →ₐ[K]
      Γ((effectiveCartierIdealSheaf D hD).subscheme, (cartierAdjunctionCutChart c).U))
    (hy' : y'.toRingHom.FormallyEtale) :
    let c' : CartierAdjunctionChart K D hD r :=
      { c with ambient := { c.ambient with coords := x', formallyEtale := hx' }, cutCoords := y', cutEtale := hy' }
    cartierAdjunctionLocalIso cX₀ hX cY₀ hY c = cartierAdjunctionLocalIso cX₀ hX cY₀ hY c' := by
  letI := c.cutNonempty
  let c' : CartierAdjunctionChart K D hD r :=
    { c with ambient := { c.ambient with coords := x', formallyEtale := hx' }, cutCoords := y', cutEtale := hy' }
  dsimp only
  obtain ⟨R, a, a', Φ, hR, ha, ha', hΦ, hΦ', _⟩ :=
    smooth_effectiveCartier_local_adjunction_coordinate_independent D hD r cX₀ hX c.ambient
      c.equation c.equation_ne_zero c.equation_spec x' hx' cY₀ hY c.cutCoords c.cutEtale y' hy'
  have h₁ := cartierAdjunctionLocalIso_unique cX₀ hX cY₀ hY c R a hR ha
  have h₂ := cartierAdjunctionLocalIso_unique cX₀ hX cY₀ hY c' R a' hR ha'
  exact (h₁.trans hΦ.symm).trans (h₂.trans hΦ'.symm).symm


/-- The chosen actual local adjunction is unchanged by ANY other
actual regular equation of the original same effective Cartier divisor. -/
theorem cartierAdjunctionLocalIso_equation_independent
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r)
    (g' : Γ(X, c.ambient.U)) (hg' : g' ≠ 0)
    (hEq' : rationalUnitClass X c.ambient.U
      (Additive.ofMul (regularEquationRationalUnit X c.ambient.U g' hg')) = D |_ c.ambient.U) :
    let c' : CartierAdjunctionChart K D hD r :=
      { c with equation := g', equation_ne_zero := hg', equation_spec := hEq' }
    cartierAdjunctionLocalIso cX₀ hX cY₀ hY c = cartierAdjunctionLocalIso cX₀ hX cY₀ hY c' := by
  letI := c.cutNonempty
  let c' : CartierAdjunctionChart K D hD r :=
    { c with equation := g', equation_ne_zero := hg', equation_spec := hEq' }
  dsimp only
  obtain ⟨R, R', a, a', Φ, hR, hR', ha, ha', hΦ, hΦ', _⟩ :=
    smooth_effectiveCartier_local_adjunction_equation_independent D hD r cX₀ hX c.ambient
      c.equation c.equation_ne_zero c.equation_spec g' hg' hEq' cY₀ hY c.cutCoords c.cutEtale
  have h₁ := cartierAdjunctionLocalIso_unique cX₀ hX cY₀ hY c R a hR ha
  have h₂ := cartierAdjunctionLocalIso_unique cX₀ hX cY₀ hY c' R' a' hR' ha'
  exact (h₁.trans hΦ.symm).trans (h₂.trans hΦ'.symm).symm


/-- Restrict actual Cartier adjunction data to any nonempty affine subopen
whose cut is nonempty. All equations and both coordinate systems are actual restrictions. -/
@[reducible]
noncomputable def cartierAdjunctionChartRestrict
    (c : CartierAdjunctionChart K D hD r) (W : X.affineOpens) [Nonempty W.1]
    (hWU : W.1 ≤ c.ambient.U)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1)] :
    CartierAdjunctionChart K D hD r where
  ambient := etaleChartAffineRestriction c.ambient W hWU
  equation := X.presheaf.map (homOfLE hWU).op c.equation
  equation_ne_zero := by
    obtain ⟨hb, _⟩ := regularEquation_restrict D hWU c.equation c.equation_ne_zero c.equation_spec
    exact hb
  equation_spec := by
    obtain ⟨hb, hEq⟩ := regularEquation_restrict D hWU c.equation c.equation_ne_zero c.equation_spec
    exact hEq
  cutNonempty := by
    change Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1)
    infer_instance
  cutCoords := (sectionOpenRestrictionAlgHom
    (show (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1 ≤
      (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ c.ambient.U from fun _x hx => hWU hx)).comp c.cutCoords
  cutEtale := RingHom.FormallyEtale.comp c.cutEtale
    (affineOpenRestriction_formallyEtale
      ⟨(cartierAdjunctionCutChart c).U, (cartierAdjunctionCutChart c).isAffine⟩
      ⟨(effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1, W.2.preimage _⟩
      (fun _x hx => hWU hx))


/-- The actual cut coordinate chart is exactly its affine restriction. -/
theorem cartierAdjunctionCutChart_restrict
    (c : CartierAdjunctionChart K D hD r) (W : X.affineOpens) [Nonempty W.1]
    (hWU : W.1 ≤ c.ambient.U)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1)] :
    cartierAdjunctionCutChart (cartierAdjunctionChartRestrict c W hWU) =
      etaleChartAffineRestriction (cartierAdjunctionCutChart c)
        ⟨(effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1, W.2.preimage _⟩
        (fun _x hx => hWU hx) := by rfl


/-- The CHOSEN actual normalized local adjunction sheaf maps agree under
arbitrary affine restriction on ALL further subopens, including empty ones. -/
theorem cartierAdjunctionLocalIso_restrict
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r)
    (W : X.affineOpens) [Nonempty W.1] (hWU : W.1 ≤ c.ambient.U)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1)] :
    let i := (effectiveCartierIdealSheaf D hD).subschemeι
    let Y := (effectiveCartierIdealSheaf D hD).subscheme
    let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
    let cW := cartierAdjunctionChartRestrict c W hWU
    ∀ (Z : Y.Opens) (hZ : Z ≤ i ⁻¹ᵁ W.1) (s : Γ(M, Z)),
      (cartierAdjunctionLocalIso cX₀ hX cY₀ hY cW).hom.val.app
          (op (Over.mk (homOfLE hZ))) s =
        (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c).hom.val.app
          (op (Over.mk (homOfLE (hZ.trans (fun _x hx => hWU hx))))) s := by
  letI := c.cutNonempty
  let i := (effectiveCartierIdealSheaf D hD).subschemeι
  let Y := (effectiveCartierIdealSheaf D hD).subscheme
  let M := (Scheme.Modules.pullback i).obj (canonicalDivisor (1 + r) cX₀ hX + D).sheaf
  let cW := cartierAdjunctionChartRestrict c W hWU
  dsimp only
  obtain ⟨R, a, R', hR, ha, hR', ha', _hnat, hcompat⟩ :=
    smooth_effectiveCartier_local_adjunction_affine_restriction D hD r c.ambient c.equation
      c.equation_ne_zero c.equation_spec W hWU c.cutCoords c.cutEtale cX₀ hX cY₀ hY
  have h₁ := cartierAdjunctionLocalIso_unique cX₀ hX cY₀ hY c R a hR ha
  have h₂ := cartierAdjunctionLocalIso_unique cX₀ hX cY₀ hY cW R'
    (Units.map (sectionOpenRestrictionAlgHom (K := K)
      (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ c.ambient.U from fun _x hx => hWU hx)).toRingHom.toMonoidHom a) hR' ha'
  have hfx := canonicalPlusCartierEquation_affine_restriction cX₀ c.ambient W hWU
    c.equation c.equation_ne_zero cW.equation_ne_zero
  have hfy := etaleChartAffineRestriction_canonical_equation cY₀ (cartierAdjunctionCutChart c)
    ⟨i ⁻¹ᵁ W.1, W.2.preimage i⟩ (fun _x hx => hWU hx)
  let KX := canonicalDivisor (1 + r) cX₀ hX
  let KY := canonicalDivisor r cY₀ hY
  let fX := etaleChartCanonicalEquation cX₀ c.ambient *
    regularEquationRationalUnit X c.ambient.U c.equation c.equation_ne_zero
  let hfX := canonicalPlusCartier_local_equation cX₀ hX c.ambient D c.equation
    c.equation_ne_zero c.equation_spec
  let fY := etaleChartCanonicalEquation cY₀ (cartierAdjunctionCutChart c)
  let hfY := (canonicalDivisor_restrict cY₀ hY (cartierAdjunctionCutChart c)).symm
  have hpull (f₁ f₂ : X.functionFieldˣ)
      (h₁ : rationalUnitClass X W.1 (Additive.ofMul f₁) = (KX + D) |_ W.1)
      (h₂ : rationalUnitClass X W.1 (Additive.ofMul f₂) = (KX + D) |_ W.1)
      (h : f₁ = f₂) :
      cartierPullbackLocalFrameIso (KX + D) i W.1 f₁ h₁ =
        cartierPullbackLocalFrameIso (KX + D) i W.1 f₂ h₂ := by
    cases h
    rfl
  have hopen (f₁ f₂ : Y.functionFieldˣ)
      (h₁ : rationalUnitClass Y (i ⁻¹ᵁ W.1) (Additive.ofMul f₁) = KY |_ (i ⁻¹ᵁ W.1))
      (h₂ : rationalUnitClass Y (i ⁻¹ᵁ W.1) (Additive.ofMul f₂) = KY |_ (i ⁻¹ᵁ W.1))
      (h : f₁ = f₂) :
      cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) f₁ h₁ = cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) f₂ h₂ := by
    cases h
    rfl
  have he : cartierAdjunctionSourceFrame cX₀ hX cW =
      moduleRestrictFrameOverIso M (i ⁻¹ᵁ W.1)
        (cartierPullbackLocalFrameIso (KX + D) i W.1 fX
          (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX)) := by
    exact congrArg (moduleRestrictFrameOverIso M (i ⁻¹ᵁ W.1))
      (hpull _ _ (canonicalPlusCartier_local_equation cX₀ hX cW.ambient D cW.equation
        cW.equation_ne_zero cW.equation_spec)
          (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX) hfx)
  have hd : cartierAdjunctionTargetFrame cY₀ hY cW =
      cartierOpenFrameIso KY (i ⁻¹ᵁ W.1) fY
        (CartierDivisor.rationalUnitClass_eq_of_le (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ c.ambient.U from fun _x hx => hWU hx) hfY) := by
    exact hopen _ _ (canonicalDivisor_restrict cY₀ hY (cartierAdjunctionCutChart cW)).symm
      (CartierDivisor.rationalUnitClass_eq_of_le (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ c.ambient.U from fun _x hx => hWU hx) hfY)
      (by simpa only [cW, cartierAdjunctionCutChart_restrict] using hfy)
  intro Z hZ s
  rw [h₁, h₂, he, hd]
  exact hcompat Z hZ s

end MixedFujita
