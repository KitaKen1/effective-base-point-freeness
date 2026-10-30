/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentAdjunctionAffineRestrictions

/-! 固定実成分の元幾何チャート・選択局所同型の一意性と全点被覆。 check-295：固定実成分の任意affine細分について、実制限環図式・両経路の同一スカラー作用・制限方程式を元スキーム射から内部供給し、任意余次元の両純正規化留数、その実チャート写像自然性、frame単元が元単元の実制限そのものであることを証明。元K_X+ΣE_iの積有理局所方程式が実affine制限で厳密に不変であることを証明し、元と細分側の実局所標準層同型を構成して、空開を含む全ての更なる部分開で写像が一致することを証明。固定成分随伴チャートを元SNC／Cartier方程式データと切断包含のみから定義し、対象エタール座標・源対象frame・選択実局所同型を内部構成。選択同型の純留数／frame単元による正規化仕様と、任意の独立な純正規化留数・単元から同じ選択同型になる一意性を証明し、元SNC幾何からこの固定成分チャート族の全点被覆も構成。選択済み同型の座標／方程式／affine比較への接続、任意二重なり一致と大域SNC随伴、数値随伴は残る。 -/

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


/-- A fixed-component adjunction chart stores ORIGINAL SNC/equation data
and containment of its cut in the actual component, with no target coords,
residue, frame unit, local iso or compatibility certificate. -/
@[reducible]
def SNCComponentAdjunctionChart
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {m r : ℕ} (ξ : Fin m → X)
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens) :=
  { c : SNCAdjunctionChart K (r := r) ξ E //
    (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ c.ambient.U ≤ U }


/-- Actual component cut coordinates are supplied internally by the original chart. -/
@[reducible]
noncomputable def sncComponentAdjunctionCutChart
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) : EtaleChart K U r := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let j := U.ι ≫ I.subschemeι
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  exact
    { U := j ⁻¹ᵁ c.1.ambient.U, isAffine := c.1.ambient.isAffine.preimage j,
      nonempty := by
        obtain ⟨p⟩ := c.1.cutNonempty
        exact ⟨⟨⟨p.val, c.2 p.prop⟩, p.prop⟩⟩,
      coords := sncComponentEtaleCoordinates c.1.ambient ξ c.1.selected c.1.snc U,
      formallyEtale := sncComponentEtaleCoordinates_formallyEtale c.1.ambient ξ c.1.selected c.1.snc U c.2 }


/-- Actual source frame of the ORIGINAL pulled K_X+SUM E_i. -/
noncomputable def sncComponentAdjunctionSourceFrame
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
    ((Scheme.Modules.pullback (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)).obj
      (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf).over (sncComponentAdjunctionCutChart ξ E U hclosed c).U ≅ SheafOfModules.unit (U.toScheme.ringCatSheaf.over (sncComponentAdjunctionCutChart ξ E U hclosed c).U) := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  exact moduleRestrictFrameOverIso _ _
    (cartierPullbackLocalFrameIso _ _ c.1.ambient.U
      (etaleChartCanonicalEquation cX₀ c.1.ambient *
        ∏ k, regularEquationRationalUnit X c.1.ambient.U (c.1.equation k) (c.1.equation_ne_zero k))
      (canonicalPlusCartierSum_local_equation cX₀ hX c.1.ambient E c.1.equation
        c.1.equation_ne_zero c.1.equation_spec))


/-- Actual target frame of ONE FIXED original canonical divisor of the component. -/
noncomputable def sncComponentAdjunctionTargetFrame
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    [IsIntegral U]
    (cY₀ : EtaleChart K U r)
    (hY : iSup (fun c : EtaleChart K U r => c.U) = ⊤)
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
    (canonicalDivisor r cY₀ hY).sheaf.over (sncComponentAdjunctionCutChart ξ E U hclosed c).U ≅
      SheafOfModules.unit (U.toScheme.ringCatSheaf.over (sncComponentAdjunctionCutChart ξ E U hclosed c).U) := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  exact cartierOpenFrameIso _ _
    (etaleChartCanonicalEquation cY₀ (sncComponentAdjunctionCutChart ξ E U hclosed c))
    (canonicalDivisor_restrict cY₀ hY (sncComponentAdjunctionCutChart ξ E U hclosed c)).symm


/-- Choose an actual normalized local canonical SHEAF isomorphism on the fixed component. -/
noncomputable def sncComponentAdjunctionLocalIso
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
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
    ((Scheme.Modules.pullback (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι)).obj
      (canonicalDivisor (m + r) cX₀ hX + ∑ k, E k).sheaf).over (sncComponentAdjunctionCutChart ξ E U hclosed c).U ≅ (canonicalDivisor r cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed)).sheaf.over (sncComponentAdjunctionCutChart ξ E U hclosed c).U := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  let hex := snc_component_cartier_sum_local_adjunction_iso ξ hsnc U hclosed E hE hI cX₀ hX
    c.1.ambient c.1.selected c.1.snc c.2 c.1.equation c.1.equation_ne_zero c.1.equation_spec cY₀
  exact Classical.choose (Classical.choose_spec (Classical.choose_spec hex)).2.2


/-- The selected local iso has a genuine pure residue and exact actual frame unit. -/
theorem sncComponentAdjunctionLocalIso_spec
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
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
    let A := Γ(X, c.1.ambient.U)
    let B := Γ(U, (sncComponentAdjunctionCutChart ξ E U hclosed c).U)
    let : Algebra A B := ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι).app c.1.ambient.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.1.ambient.U
    ∃ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K], R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun k : Fin m => KaehlerDifferential.D K A (c.1.equation k)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis c.1.ambient.coords c.1.ambient.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r
            (etaleCoordinateBasis (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
              (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale) ∧
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c) = moduleOverFrameWeightedIso _ _ (sncComponentAdjunctionCutChart ξ E U hclosed c).U
        (sncComponentAdjunctionSourceFrame ξ E U hclosed cX₀ hX c) (sncComponentAdjunctionTargetFrame ξ E U hclosed cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed) c) a := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  let hex := snc_component_cartier_sum_local_adjunction_iso ξ hsnc U hclosed E hE hI cX₀ hX
    c.1.ambient c.1.selected c.1.snc c.2 c.1.equation c.1.equation_ne_zero c.1.equation_spec cY₀
  let R := Classical.choose hex
  let a := Classical.choose (Classical.choose_spec hex)
  have h := Classical.choose_spec (Classical.choose_spec hex)
  dsimp only
  refine ⟨R, a, h.1, h.2.1, ?_⟩
  exact moduleOverFrameWeightedIso_unique _ _ (sncComponentAdjunctionCutChart ξ E U hclosed c).U
    (sncComponentAdjunctionSourceFrame ξ E U hclosed cX₀ hX c) (sncComponentAdjunctionTargetFrame ξ E U hclosed cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed) c) a (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c)
      (by simpa only [sncComponentAdjunctionLocalIso, sncComponentAdjunctionSourceFrame,
        sncComponentAdjunctionTargetFrame, sncComponentAdjunctionCutChart, hex, R, a] using
          (Classical.choose_spec h.2.2).1.1)


/-- ANY independently constructed pure-normalized residue and frame unit give
exactly the chosen actual local SHEAF iso, without a compatibility input. -/
theorem sncComponentAdjunctionLocalIso_unique
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
    (c : SNCComponentAdjunctionChart K (r := r) ξ E U) :
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
            (etaleCoordinateBasis (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
              (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale) →
      (sncComponentAdjunctionLocalIso ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c) = moduleOverFrameWeightedIso _ _ (sncComponentAdjunctionCutChart ξ E U hclosed c).U
        (sncComponentAdjunctionSourceFrame ξ E U hclosed cX₀ hX c) (sncComponentAdjunctionTargetFrame ξ E U hclosed cY₀ (snc_component_etaleChart_cover ξ hsnc E hE U hclosed) c) a := by
  letI := (sncComponentAdjunctionCutChart ξ E U hclosed c).nonempty
  let A := Γ(X, c.1.ambient.U)
  let B := Γ(U, (sncComponentAdjunctionCutChart ξ E U hclosed c).U)
  let : Algebra A B := ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι).app c.1.ambient.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.1.ambient.U
  dsimp only
  intro R a hR ha
  obtain ⟨R₀, a₀, hR₀, ha₀, hΦ⟩ := sncComponentAdjunctionLocalIso_spec ξ E U hclosed hsnc hE hI cX₀ hX cY₀ c
  have hsurj := (snc_component_affine_quotient_data c.1.ambient ξ c.1.selected c.1.snc U c.2).1
  obtain ⟨_heq, hu⟩ := pure_complete_intersection_residue_frame_unique m r c.1.equation hsurj
    (etaleCoordinateBasis c.1.ambient.coords c.1.ambient.formallyEtale)
    (etaleCoordinateBasis (sncComponentAdjunctionCutChart ξ E U hclosed c).coords
      (sncComponentAdjunctionCutChart ξ E U hclosed c).formallyEtale)
    R₀ R a₀ a hR₀ hR ha₀ ha
  rw [hu] at hΦ
  exact hΦ


/-- ORIGINAL SNC geometry and actual Cartier equations supply a fixed-component
chart through EVERY component point, with internal target coordinates. -/
theorem exists_sncComponentAdjunctionChart_at
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X) (hE : ∀ k, (E k).IsEffective)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    (p : U) :
    ∃ c : SNCComponentAdjunctionChart K (r := r) ξ E U,
      p ∈ (sncComponentAdjunctionCutChart ξ E U hclosed c).U := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  obtain ⟨O, _hO, hOU⟩ := inducing_relative_open_lift I.subschemeι.isClosedEmbedding.isInducing
    (⊤ : X.Opens) U (by intro z hz; trivial)
  have hpO : I.subschemeι (U.ι p) ∈ O := by
    change U.ι p ∈ I.subschemeι ⁻¹ᵁ O
    rw [hOU]
    exact p.prop
  obtain ⟨c, τ, g, hg, hp, hcO, hc, hEq⟩ := snc_stratum_exists_cartier_equation_chart_at
    ξ hsnc E hE (U.ι p) O hpO
  have hcut : I.subschemeι ⁻¹ᵁ c.U ≤ U := by
    rw [← hOU]
    exact fun _z hz => hcO hz
  let d : SNCAdjunctionChart K (r := r) ξ E :=
    { ambient := c, selected := τ, snc := hc, equation := g, equation_ne_zero := hg,
      equation_spec := hEq, cutNonempty := ⟨⟨U.ι p, hp⟩⟩ }
  exact ⟨⟨d, hcut⟩, hp⟩


/-- The entire ACTUAL fixed component is covered by original-data adjunction
charts. No supplied compatible atlas, local maps or gluing certificate. -/
theorem sncComponentAdjunctionChart_cover
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X) (hE : ∀ k, (E k).IsEffective)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme)) :
    iSup (fun c : SNCComponentAdjunctionChart K (r := r) ξ E U =>
      (sncComponentAdjunctionCutChart ξ E U hclosed c).U) = ⊤ := by
  apply top_unique
  intro p _hp
  obtain ⟨c, hc⟩ := exists_sncComponentAdjunctionChart_at ξ hsnc E hE U hclosed p
  exact Opens.mem_iSup.mpr ⟨c, hc⟩

end MixedFujita
