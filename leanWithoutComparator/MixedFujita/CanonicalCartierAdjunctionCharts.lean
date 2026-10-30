/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierAdjunctionAffineRestrictions

/-! 実Cartier随伴チャートと選択局所同型の正規化一意性。 check-287：実周囲etale座標・実正則Cartier方程式・実切断座標だけを持つ局所チャートを定義し、既存の実局所標準随伴層同型を選ぶ。純正規化留数の一意性と最高次楔積の係数単射性から、独立構成した任意の正規化留数・frame単元でも同じ選択局所同型になることを証明。選択済み同型について周囲／切断の同時座標変更と正則方程式変更からの独立性、任意affine細分での全部分開制限一致を証明。共通affine細分における二同型の一致を導き、切断の一般点を含む一つの共通affine開とTauCetiの実線束制限の単射性から、任意二チャートの重なりの全ての部分開で元の実層写像が一致することを証明。空開も含む。全点を覆う局所チャートの存在の接続、大域留数層同型の貼合せ、SNC反復随伴、数値随伴は残る。 -/

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



/-- Actual local coordinate and regular-equation data for a Cartier cut.
No residue, frame unit, sheaf map or compatibility certificate is supplied. -/
structure CartierAdjunctionChart
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (D : CartierDivisor X) (hD : D.IsEffective)
    [(effectiveCartierIdealSheaf D hD).subscheme.Over (Spec (CommRingCat.of K))] (r : ℕ) where
  ambient : EtaleChart K X (1 + r)
  equation : Γ(X, ambient.U)
  equation_ne_zero : equation ≠ 0
  equation_spec : rationalUnitClass X ambient.U
    (Additive.ofMul (regularEquationRationalUnit X ambient.U equation equation_ne_zero)) = D |_ ambient.U
  cutNonempty : Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ ambient.U)
  cutCoords : MvPolynomial (Fin r) K →ₐ[K]
    Γ((effectiveCartierIdealSheaf D hD).subscheme,
      (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ ambient.U)
  cutEtale : cutCoords.toRingHom.FormallyEtale


/-- The cut coordinates give an actual affine etale chart. -/
@[reducible]
noncomputable def cartierAdjunctionCutChart (c : CartierAdjunctionChart K D hD r) :
    EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r where
  U := (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ c.ambient.U
  isAffine := c.ambient.isAffine.preimage _
  nonempty := c.cutNonempty
  coords := c.cutCoords
  formallyEtale := c.cutEtale


/-- Actual source Cartier pullback frame for the original K_X+D. -/
noncomputable def cartierAdjunctionSourceFrame
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r) :
    ((Scheme.Modules.pullback (effectiveCartierIdealSheaf D hD).subschemeι).obj
        (canonicalDivisor (1 + r) cX₀ hX + D).sheaf).over (cartierAdjunctionCutChart c).U ≅
      SheafOfModules.unit ((effectiveCartierIdealSheaf D hD).subscheme.ringCatSheaf.over (cartierAdjunctionCutChart c).U) := by
  letI := c.cutNonempty
  exact moduleRestrictFrameOverIso _ _
    (cartierPullbackLocalFrameIso _ _ c.ambient.U
      (etaleChartCanonicalEquation cX₀ c.ambient *
        regularEquationRationalUnit X c.ambient.U c.equation c.equation_ne_zero)
      (canonicalPlusCartier_local_equation cX₀ hX c.ambient D c.equation
        c.equation_ne_zero c.equation_spec))


/-- Actual target frame for the original canonical Cartier divisor of the cut. -/
noncomputable def cartierAdjunctionTargetFrame
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r) :
    (canonicalDivisor r cY₀ hY).sheaf.over (cartierAdjunctionCutChart c).U ≅
      SheafOfModules.unit ((effectiveCartierIdealSheaf D hD).subscheme.ringCatSheaf.over (cartierAdjunctionCutChart c).U) :=
  by
  letI := c.cutNonempty
  exact cartierOpenFrameIso _ _ (etaleChartCanonicalEquation cY₀ (cartierAdjunctionCutChart c))
    (canonicalDivisor_restrict cY₀ hY (cartierAdjunctionCutChart c)).symm


/-- Choose the actual normalized local canonical adjunction sheaf isomorphism. -/
noncomputable def cartierAdjunctionLocalIso
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r) :
    ((Scheme.Modules.pullback (effectiveCartierIdealSheaf D hD).subschemeι).obj
        (canonicalDivisor (1 + r) cX₀ hX + D).sheaf).over (cartierAdjunctionCutChart c).U ≅
      (canonicalDivisor r cY₀ hY).sheaf.over (cartierAdjunctionCutChart c).U := by
  letI := c.cutNonempty
  let hex := smooth_effectiveCartier_local_adjunction_iso D hD r cX₀ hX c.ambient c.equation
    c.equation_ne_zero c.equation_spec cY₀ hY c.cutCoords c.cutEtale
  exact Classical.choose (Classical.choose_spec (Classical.choose_spec hex)).2.2


/-- Its actual pure residue normalization and canonical-frame coefficient. -/
theorem cartierAdjunctionLocalIso_spec
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r) :
    let A := Γ(X, c.ambient.U)
    let B := Γ((effectiveCartierIdealSheaf D hD).subscheme, (cartierAdjunctionCutChart c).U)
    let : Algebra A B := ((effectiveCartierIdealSheaf D hD).subschemeι.app c.ambient.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.ambient.U
    ∃ (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K], R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A c.equation) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis c.ambient.coords c.ambient.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis c.cutCoords c.cutEtale) ∧
      (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c) = moduleOverFrameWeightedIso _ _ (cartierAdjunctionCutChart c).U
        ((cartierAdjunctionSourceFrame cX₀ hX c)) ((cartierAdjunctionTargetFrame cY₀ hY c)) a := by
  letI := c.cutNonempty
  let hex := smooth_effectiveCartier_local_adjunction_iso D hD r cX₀ hX c.ambient c.equation
    c.equation_ne_zero c.equation_spec cY₀ hY c.cutCoords c.cutEtale
  let R := Classical.choose hex
  let a := Classical.choose (Classical.choose_spec hex)
  have h := Classical.choose_spec (Classical.choose_spec hex)
  dsimp only
  refine ⟨R, a, h.1, h.2.1, ?_⟩
  exact moduleOverFrameWeightedIso_unique _ _ (cartierAdjunctionCutChart c).U
    ((cartierAdjunctionSourceFrame cX₀ hX c)) ((cartierAdjunctionTargetFrame cY₀ hY c)) a ((cartierAdjunctionLocalIso cX₀ hX cY₀ hY c))
      (by simpa only [cartierAdjunctionLocalIso, cartierAdjunctionSourceFrame,
        cartierAdjunctionTargetFrame, cartierAdjunctionCutChart, hex, R, a] using
          (Classical.choose_spec h.2.2).1.1)


/-- Every independently constructed pure-normalized residue and frame unit
produce exactly the chosen actual local adjunction SHEAF iso. -/
theorem cartierAdjunctionLocalIso_unique
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤)
    (c : CartierAdjunctionChart K D hD r) :
    let A := Γ(X, c.ambient.U)
    let B := Γ((effectiveCartierIdealSheaf D hD).subscheme, (cartierAdjunctionCutChart c).U)
    let : Algebra A B := ((effectiveCartierIdealSheaf D hD).subschemeι.app c.ambient.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.ambient.U
    ∀ (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K], R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A c.equation) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) →
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis c.ambient.coords c.ambient.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis c.cutCoords c.cutEtale) →
      (cartierAdjunctionLocalIso cX₀ hX cY₀ hY c) = moduleOverFrameWeightedIso _ _ (cartierAdjunctionCutChart c).U
        ((cartierAdjunctionSourceFrame cX₀ hX c)) ((cartierAdjunctionTargetFrame cY₀ hY c)) a := by
  letI := c.cutNonempty
  let A := Γ(X, c.ambient.U)
  let B := Γ((effectiveCartierIdealSheaf D hD).subscheme, (cartierAdjunctionCutChart c).U)
  let : Algebra A B := ((effectiveCartierIdealSheaf D hD).subschemeι.app c.ambient.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower _ c.ambient.U
  dsimp only
  intro R a hR ha
  obtain ⟨R₀, a₀, hR₀, ha₀, hΦ⟩ := cartierAdjunctionLocalIso_spec cX₀ hX cY₀ hY c
  have hsurj := (effectiveCartier_affine_principal_quotient_data D hD
    ⟨c.ambient.U, c.ambient.isAffine⟩ c.equation c.equation_ne_zero c.equation_spec).2.1
  have heq := pure_pulled_canonical_residue_unique c.equation hsurj r R₀ R hR₀ hR
  rw [heq] at ha₀
  have hu : a₀ = a := Units.ext
    (topExterior_wedge_smul_cancel (etaleCoordinateBasis c.cutCoords c.cutEtale) (ha₀.symm.trans ha))
  rw [hu] at hΦ
  exact hΦ

end MixedFujita
