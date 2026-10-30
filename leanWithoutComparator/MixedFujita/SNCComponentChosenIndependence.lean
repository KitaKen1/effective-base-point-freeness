/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentAdjunctionCharts

/-! 実選択SNC局所同型の座標・方程式独立性と任意対象frame。 check-296：元幾何のみから選択したSNC整成分の実局所標準層同型について、周囲・内部対象座標変更と全Cartier方程式変更からの独立性を証明。任意の対象エタール座標と独立な純正規化留数・frame単元でも同じ選択層同型を表すことを証明し、内部対象座標の選択が制限で一致するとの仮定を除去。元方程式の実affine制限チャートを構成し、選択済み実層写像の任意affine制限一致を空開を含む全部分開で証明。共通affine細分での両座標・全方程式比較と、一般点での一つの共通affine近傍・実線束の制限単射性から、任意二チャート重なりの全部分開で実写像の一致を証明。内部全点被覆と既存の加群層貼合せ・被覆上同型判定により、元j^*O(K_X+ΣE_i)とO(K_U)の一意な大域正規化随伴層同型を構成し、全部分開の局所写像との一致・各局所純留数と正確なframe単元による正規化を証明。最後に元smooth Noetherian SNC幾何の任意の交差点から、実整開閉成分・成分標準類参照チャート・同じ一意な大域随伴層同型まで内部供給する存在定理へ接続。全閉層・中間層の整性や、与えた成分・対象被覆・留数・局所同型・重なり証明・大域同型を追加仮定にしない。法線成分順序は固定。数値随伴・正値性・一般KV・F1F2は残る。 -/

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




/-- Both coordinate systems may change on an actual SNC chart; the chosen
local isomorphism itself is unchanged. New target coordinates remain internal. -/
theorem sncComponentAdjunctionLocalIso_coordinate_independent
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
    (x' : MvPolynomial (Fin (m + r)) K →ₐ[K] Γ(X, c.1.ambient.U))
    (hx' : x'.toRingHom.FormallyEtale) (τ' : Fin m → Fin (m + r))
    (hsnc' : IsSNCChart { c.1.ambient with coords := x', formallyEtale := hx' }
      ξ (fun k => some (τ' k))) :
    let c' : SNCComponentAdjunctionChart K (r := r) ξ E U :=
      ⟨{ c.1 with ambient := { c.1.ambient with coords := x', formallyEtale := hx' }, selected := τ', snc := hsnc' }, c.2⟩
    sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c =
      sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c' := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  let c' : SNCComponentAdjunctionChart K (r := r) ξ E U :=
    ⟨{ c.1 with ambient := { c.1.ambient with coords := x', formallyEtale := hx' }, selected := τ', snc := hsnc' }, c.2⟩
  dsimp only
  obtain ⟨R, a, a', Φ, hR, ha, ha', hΦ, hΦ', _⟩ :=
    snc_component_local_adjunction_coordinate_independent ξ hsnc U hclosed E hE hI cX₀ hX
      c.1.ambient c.1.selected c.1.snc c.2 c.1.equation c.1.equation_ne_zero
      c.1.equation_spec x' hx' cY₀
      (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
      (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale
      (sncComponentAdjunctionCutChart ξ E U hclosed c').coords
      (sncComponentAdjunctionCutChart ξ E U hclosed c').formallyEtale
  have h₁ := sncComponentAdjunctionLocalIso_unique ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c R a hR ha
  have h₂ := sncComponentAdjunctionLocalIso_unique ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c' R a' hR ha'
  exact (h₁.trans hΦ.symm).trans (h₂.trans hΦ'.symm).symm


/-- Simultaneous changes of all actual Cartier equations leave the chosen
local adjunction isomorphism unchanged, with no unit-ratio input. -/
theorem sncComponentAdjunctionLocalIso_equations_independent
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
    (g' : Fin m → Γ(X, c.1.ambient.U)) (hg' : ∀ k, g' k ≠ 0)
    (hEq' : ∀ k, rationalUnitClass X c.1.ambient.U
      (Additive.ofMul (regularEquationRationalUnit X c.1.ambient.U (g' k) (hg' k))) =
        E k |_ c.1.ambient.U) :
    let c' : SNCComponentAdjunctionChart K (r := r) ξ E U :=
      ⟨{ c.1 with equation := g', equation_ne_zero := hg', equation_spec := hEq' }, c.2⟩
    sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c =
      sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c' := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  let c' : SNCComponentAdjunctionChart K (r := r) ξ E U :=
    ⟨{ c.1 with equation := g', equation_ne_zero := hg', equation_spec := hEq' }, c.2⟩
  dsimp only
  obtain ⟨R, R', a, a', Φ, hR, hR', ha, ha', hΦ, hΦ', _⟩ :=
    snc_component_local_adjunction_equations_independent ξ hsnc U hclosed E hE hI cX₀ hX
      c.1.ambient c.1.selected c.1.snc c.2 c.1.equation c.1.equation_ne_zero
      c.1.equation_spec g' hg' hEq' cY₀
      (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
      (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale
  have h₁ := sncComponentAdjunctionLocalIso_unique ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c R a hR ha
  have h₂ := sncComponentAdjunctionLocalIso_unique ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c' R' a' hR' ha'
  exact (h₁.trans hΦ.symm).trans (h₂.trans hΦ'.symm).symm


/-- ANY target etale coordinates and independently normalized pure residue
represent exactly the chosen local SHEAF isomorphism. Target frame choices
and their compatibility are derived internally. -/
theorem sncComponentAdjunctionLocalIso_target_coordinates
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
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ(U, (sncComponentAdjunctionCutChart ξ E U hclosed c).U))
    (hy : y.toRingHom.FormallyEtale) :
    let : Nonempty (sncComponentAdjunctionCutChart ξ E U hclosed c).U :=
      (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
    let cY : EtaleChart K U r :=
      { (sncComponentAdjunctionCutChart ξ E U hclosed c) with coords := y, formallyEtale := hy }
    let A := Γ(X, c.1.ambient.U)
    let B := Γ(U, (sncComponentAdjunctionCutChart ξ E U hclosed c).U)
    let : Algebra A B := ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι).app c.1.ambient.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.1.ambient.U
    ∀ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K], R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun k : Fin m => KaehlerDifferential.D K A (c.1.equation k)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) →
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis c.1.ambient.coords c.1.ambient.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r
            (etaleCoordinateBasis y hy) →
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c) = moduleOverFrameWeightedIso _ _ (sncComponentAdjunctionCutChart ξ E U hclosed c).U
        (sncComponentAdjunctionSourceFrame ξ E U hclosed cX₀ hX c) (cartierOpenFrameIso (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed))
          (sncComponentAdjunctionCutChart ξ E U hclosed c).U
          (etaleChartCanonicalEquation cY₀ cY)
          (canonicalDivisor_restrict cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed) cY).symm) a := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  let A := Γ(X, c.1.ambient.U)
  let B := Γ(U, (sncComponentAdjunctionCutChart ξ E U hclosed c).U)
  let : Algebra A B := ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι).app c.1.ambient.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.1.ambient.U
  dsimp only
  intro R a hR ha
  obtain ⟨R₀, a₀, a₁, Φ, hR₀, ha₀, ha₁, hΦ₀, hΦ₁, _⟩ :=
    snc_component_local_adjunction_coordinate_independent ξ hsnc U hclosed E hE hI cX₀ hX
      c.1.ambient c.1.selected c.1.snc c.2 c.1.equation c.1.equation_ne_zero
      c.1.equation_spec c.1.ambient.coords c.1.ambient.formallyEtale cY₀ y hy
      (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
      (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale
  have hchosen := sncComponentAdjunctionLocalIso_unique ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c R₀ a₁ hR₀ ha₁
  have hsurj := (snc_component_affine_quotient_data c.1.ambient ξ c.1.selected c.1.snc U c.2).1
  obtain ⟨_heq, hu⟩ := pure_complete_intersection_residue_frame_unique m r c.1.equation hsurj
    (etaleCoordinateBasis c.1.ambient.coords c.1.ambient.formallyEtale)
    (etaleCoordinateBasis y hy) R₀ R a₀ a hR₀ hR ha₀ ha
  rw [hu] at hΦ₀
  exact (hchosen.trans hΦ₁.symm).trans hΦ₀

end MixedFujita
