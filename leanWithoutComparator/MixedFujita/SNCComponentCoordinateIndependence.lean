/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CompleteIntersectionFrameUniqueness

/-! 元SNC整成分の実局所標準層同型の両座標独立性。 check-294：固定した法線成分順序について、任意に独立構成した純正規化完全交差留数と実標準frame単元の一致を証明。元Cartier方程式を個別の単元倍に同時変更したとき、実有理局所方程式の積が全単元比の積で変換する厳密公式を証明。元SNC整成分上の同じaffine開で周囲と対象の両エタール座標を同時変更しても、実局所標準層同型が一致することを、実Jacobian単元と源・対象frame係数の相殺から内部構成。全元Cartier因子の二組の実局所方程式から各単元比・二留数・二frame単元を内部構成し、その積による留数係数と源frame変化の相殺から同じ実局所標準層同型を得ることを証明。両比較は空開を含む全部分開の正確な係数則を持ち、比較一致や単元変換証明を追加入力にしない。異なるaffine開への制限比較、任意二チャート重なりと大域SNC随伴、数値随伴は残る。 -/

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


/-- Simultaneously changing BOTH ambient and cut coordinates on the SAME
actual affine Cartier chart gives the SAME normalized actual local adjunction
SHEAF iso. All Jacobian units and their source/target frame laws are derived
internally from the original coordinates, not compatibility certificates. -/
theorem snc_component_local_adjunction_coordinate_independent
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    [IsIntegral U] (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X)) (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cX : EtaleChart K X (m + r))
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart cX ξ (fun i => some (τ i)))
    (hcut : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ cX.U ≤ U)
    (g : Fin m → Γ(X, cX.U)) (hg : ∀ i, g i ≠ 0)
    (hEq : ∀ i, rationalUnitClass X cX.U
      (Additive.ofMul (regularEquationRationalUnit X cX.U (g i) (hg i))) = E i |_ cX.U)
    (x' : MvPolynomial (Fin (m + r)) K →ₐ[K] Γ(X, cX.U))
    (hx' : x'.toRingHom.FormallyEtale)
    [Nonempty ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U)]
    (cY₀ : EtaleChart K U r)
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ(U, (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U))
    (hy : y.toRingHom.FormallyEtale)
    (y' : MvPolynomial (Fin r) K →ₐ[K]
      Γ(U, (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U))
    (hy' : y'.toRingHom.FormallyEtale) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let Y : Scheme := U
    let i := U.ι ≫ I.subschemeι
    let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
      (by rw [Scheme.Opens.range_ι]; exact hclosed)
    let V := i ⁻¹ᵁ cX.U
    let A := Γ(X, cX.U)
    let B := Γ(Y, V)
    let : Algebra A B := (i.app cX.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
    let cY : EtaleChart K Y r :=
      { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
        coords := y, formallyEtale := hy }
    let cX' : EtaleChart K X (m + r) := { cX with coords := x', formallyEtale := hx' }
    let cY' : EtaleChart K Y r := { cY with coords := y', formallyEtale := hy' }
    let KX := canonicalDivisor (m + r) cX₀ hX
    let hY := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
    let KY := canonicalDivisor r cY₀ hY
    let M := (Scheme.Modules.pullback i).obj (KX + ∑ i, E i).sheaf
    let e := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + ∑ i, E i) i cX.U
        (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i))
        (canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq))
    let e' := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + ∑ i, E i) i cX.U
        (etaleChartCanonicalEquation cX₀ cX' * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i))
        (canonicalPlusCartierSum_local_equation cX₀ hX cX' E g hg hEq))
    let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
      (canonicalDivisor_restrict cY₀ hY cY).symm
    let d' := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY')
      (canonicalDivisor_restrict cY₀ hY cY').symm
    ∃ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
      (a a' : Bˣ) (Φ : M.over V ≅ KY.sheaf.over V),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => KaehlerDifferential.D K A (g i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis x' hx')) =
          (a' : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y' hy') ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e d a ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e' d' a' ∧
      ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
        (moduleOverFrameCoefficient KY.sheaf V d W hWV
            (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
          Y.presheaf.map (homOfLE hWV).op ↑a * moduleOverFrameCoefficient M V e W hWV s) ∧
        (moduleOverFrameCoefficient KY.sheaf V d' W hWV
            (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
          Y.presheaf.map (homOfLE hWV).op ↑a' * moduleOverFrameCoefficient M V e' W hWV s) := by
  classical
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let Y : Scheme := U
  let i := U.ι ≫ I.subschemeι
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  let V := i ⁻¹ᵁ cX.U
  let A := Γ(X, cX.U)
  let B := Γ(Y, V)
  let : Algebra A B := (i.app cX.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
  let cY : EtaleChart K Y r :=
    { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
      coords := y, formallyEtale := hy }
  let cX' : EtaleChart K X (m + r) := { cX with coords := x', formallyEtale := hx' }
  let cY' : EtaleChart K Y r := { cY with coords := y', formallyEtale := hy' }
  let KX := canonicalDivisor (m + r) cX₀ hX
  let hY := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + ∑ i, E i).sheaf
  let e := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + ∑ i, E i) i cX.U
      (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i))
      (canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq))
  let e' := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + ∑ i, E i) i cX.U
      (etaleChartCanonicalEquation cX₀ cX' * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i))
      (canonicalPlusCartierSum_local_equation cX₀ hX cX' E g hg hEq))
  let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
    (canonicalDivisor_restrict cY₀ hY cY).symm
  let d' := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY')
    (canonicalDivisor_restrict cY₀ hY cY').symm
  let b : Module.Basis (Fin (m + r)) A Ω[A⁄K] :=
    etaleCoordinateBasis cX.coords cX.formallyEtale
  let b' : Module.Basis (Fin (m + r)) A Ω[A⁄K] := etaleCoordinateBasis x' hx'
  let c : Module.Basis (Fin r) B Ω[B⁄K] := etaleCoordinateBasis y hy
  let c' : Module.Basis (Fin r) B Ω[B⁄K] := etaleCoordinateBasis y' hy'
  let uX : Aˣ := (Module.Basis.isUnit_det b' b).unit
  let uY : Bˣ := (Module.Basis.isUnit_det c' c).unit
  obtain ⟨R, a, hR, ha⟩ := snc_component_cartier_sum_residue_canonical_frame
    cX ξ τ hc U hcut E hE hI g hg hEq y hy
  obtain ⟨a', haval, ha'⟩ := pulled_canonical_residue_two_frame_transition b b' c c' R.toLinearMap a ha
  have hscalar : (a' : B) * i.app cX.U ↑uX = (uY : B) * (a : B) := by
    have hux : (uX : A) = b'.det b := IsUnit.unit_spec _
    have huy : (uY : B) = c'.det c := IsUnit.unit_spec _
    have hinv : b.det b' * b'.det b = (1 : A) :=
      (Module.Basis.det_mul_det b b' b).trans (Module.Basis.det_self b)
    change (a' : B) * algebraMap A B ↑uX = (uY : B) * (a : B)
    rw [haval, hux, huy]
    calc
      _ = (algebraMap A B (b.det b') * algebraMap A B (b'.det b)) *
          (c'.det c * (a : B)) := by ring
      _ = _ := by rw [← map_mul, hinv, map_one, one_mul]
  have hfx : etaleChartCanonicalEquation cX₀ cX' =
      Units.map (X.germToFunctionField cX.U).hom uX * etaleChartCanonicalEquation cX₀ cX :=
    etaleChartCanonicalEquation_same_open_change cX₀ cX x' hx'
  have hfy : etaleChartCanonicalEquation cY₀ cY' =
      Units.map (Y.germToFunctionField V).hom uY * etaleChartCanonicalEquation cY₀ cY :=
    etaleChartCanonicalEquation_same_open_change cY₀ cY y' hy'
  have hfunit :
      etaleChartCanonicalEquation cX₀ cX' * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i) =
        Units.map (X.germToFunctionField cX.U).hom uX *
          (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i)) := by
    rw [hfx]
    exact mul_assoc _ _ _
  have he : ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
      moduleOverFrameCoefficient M V e' W hWV s =
        Y.presheaf.map (homOfLE hWV).op (i.app cX.U ↑uX) *
          moduleOverFrameCoefficient M V e W hWV s := by
    intro W hWV s
    exact cartierPullbackFrameCoefficient_unit_equation_change (KX + ∑ i, E i) i cX.U
      _ _ (canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq)
      (canonicalPlusCartierSum_local_equation cX₀ hX cX' E g hg hEq) uX hfunit W hWV s
  have hd : ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(KY.sheaf, W)),
      moduleOverFrameCoefficient KY.sheaf V d' W hWV s =
        Y.presheaf.map (homOfLE hWV).op (uY : B) *
          moduleOverFrameCoefficient KY.sheaf V d W hWV s := by
    intro W hWV s
    exact cartierOpenFrameCoefficient_unit_equation_change KY V _ _
      (canonicalDivisor_restrict cY₀ hY cY).symm
      (canonicalDivisor_restrict cY₀ hY cY').symm uY hfy W hWV s
  let Φ := moduleOverFrameWeightedIso M KY.sheaf V e d a
  have hΦ : moduleOverFrameWeightedIso M KY.sheaf V e' d' a' = Φ :=
    moduleWeightedFrameIso_cancel_both_changes M KY.sheaf V e e' d d' a a'
      (i.app cX.U ↑uX) (uY : B) hscalar he hd
  dsimp only
  refine ⟨R, a, a', Φ, hR, ha, ha', rfl, hΦ.symm, ?_⟩
  intro W hWV s
  constructor
  · exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e d a W hWV s
  · rw [← hΦ]
    exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e' d' a' W hWV s

end MixedFujita
