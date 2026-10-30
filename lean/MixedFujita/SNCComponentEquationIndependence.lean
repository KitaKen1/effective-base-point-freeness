/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentCoordinateIndependence

/-! 全元Cartier方程式の単元積変更からの実局所層同型独立性。 check-294：固定した法線成分順序について、任意に独立構成した純正規化完全交差留数と実標準frame単元の一致を証明。元Cartier方程式を個別の単元倍に同時変更したとき、実有理局所方程式の積が全単元比の積で変換する厳密公式を証明。元SNC整成分上の同じaffine開で周囲と対象の両エタール座標を同時変更しても、実局所標準層同型が一致することを、実Jacobian単元と源・対象frame係数の相殺から内部構成。全元Cartier因子の二組の実局所方程式から各単元比・二留数・二frame単元を内部構成し、その積による留数係数と源frame変化の相殺から同じ実局所標準層同型を得ることを証明。両比較は空開を含む全部分開の正確な係数則を持ち、比較一致や単元変換証明を追加入力にしない。異なるaffine開への制限比較、任意二チャート重なりと大域SNC随伴、数値随伴は残る。 -/

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


/-- Two ACTUAL regular equations of the same Cartier cut produce the SAME
normalized local Cartier adjunction SHEAF iso. Equation unit, both residues,
both frame units and their cancellation are all constructed internally from
the original geometry; no unit-change or compatibility certificate is input. -/
theorem snc_component_local_adjunction_equations_independent
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
    (g' : Fin m → Γ(X, cX.U)) (hg' : ∀ i, g' i ≠ 0)
    (hEq' : ∀ i, rationalUnitClass X cX.U
      (Additive.ofMul (regularEquationRationalUnit X cX.U (g' i) (hg' i))) = E i |_ cX.U)
    [Nonempty ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U)]
    (cY₀ : EtaleChart K U r)
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ(U, (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U))
    (hy : y.toRingHom.FormallyEtale) :
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
        (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g' i) (hg' i))
        (canonicalPlusCartierSum_local_equation cX₀ hX cX E g' hg' hEq'))
    let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
      (canonicalDivisor_restrict cY₀ hY cY).symm
    ∃ (R R' : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
      (a a' : Bˣ) (Φ : M.over V ≅ KY.sheaf.over V),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => KaehlerDifferential.D K A (g i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => KaehlerDifferential.D K A (g' i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a' : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e d a ∧
      Φ = moduleOverFrameWeightedIso M KY.sheaf V e' d a' ∧
      ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
        (moduleOverFrameCoefficient KY.sheaf V d W hWV
            (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
          Y.presheaf.map (homOfLE hWV).op ↑a * moduleOverFrameCoefficient M V e W hWV s) ∧
        (moduleOverFrameCoefficient KY.sheaf V d W hWV
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
      (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g' i) (hg' i))
      (canonicalPlusCartierSum_local_equation cX₀ hX cX E g' hg' hEq'))
  let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
    (canonicalDivisor_restrict cY₀ hY cY).symm
  obtain ⟨u, hu⟩ : ∃ u : Fin m → Aˣ, ∀ k, g' k = (u k : A) * g k := by
    choose u hu using fun k => effectiveCartier_affine_equations_unit (E k) (hE k)
      ⟨cX.U, cX.isAffine⟩ (g k) (g' k) (hg k) (hg' k) (hEq k) (hEq' k)
    exact ⟨u, hu⟩
  let v : Aˣ := ∏ k, u k
  obtain ⟨R, a, hR, ha⟩ := snc_component_cartier_sum_residue_canonical_frame
    cX ξ τ hc U hcut E hE hI g hg hEq y hy
  obtain ⟨R', a', hR', ha'⟩ := snc_component_cartier_sum_residue_canonical_frame
    cX ξ τ hc U hcut E hE hI g' hg' hEq' y hy
  obtain ⟨hsurj, hker⟩ := snc_component_affine_quotient_data cX ξ τ hc U hcut
  obtain ⟨w, hw⟩ := snc_original_cartier_equations_units cX ξ τ hc E hE hI g hg hEq
  have hcoordzero (k : Fin m) : algebraMap A B (cX.coords (MvPolynomial.X (τ k))) = 0 :=
    RingHom.mem_ker.mp (hker ▸ Ideal.subset_span (Set.mem_range_self k))
  have hgzero (k : Fin m) : algebraMap A B (g k) = 0 := by
    rw [hw k, map_mul, hcoordzero, mul_zero]
  have hRunit : ∀ z : Fin r → Ω[A⁄K],
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun k : Fin m => KaehlerDifferential.D K A ((u k : A) * g k)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z) := by
    intro z
    have hn : (fun k : Fin m => KaehlerDifferential.D K A ((u k : A) * g k)) =
        fun k : Fin m => KaehlerDifferential.D K A (g' k) :=
      funext fun k => (congrArg (KaehlerDifferential.D K A) (hu k)).symm
    rw [hn]
    exact hR' z
  have hres := pure_complete_intersection_residue_equations_change m r g
    (fun k => (u k : A)) hgzero hsurj (etaleCoordinateBasis cX.coords cX.formallyEtale) R R' hR hRunit
  have hscalar : (a' : B) * i.app cX.U ↑v = (a : B) := by
    have h := hres ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
      (etaleCoordinateBasis cX.coords cX.formallyEtale))
    rw [map_smul, ha', ha] at h
    have hh : algebraMap A B (∏ k, (u k : A)) * (a' : B) = (a : B) :=
      topExterior_wedge_smul_cancel (etaleCoordinateBasis y hy)
        (by simpa only [smul_smul] using h)
    change (a' : B) * algebraMap A B ↑v = (a : B)
    have hv : (v : A) = ∏ k, (u k : A) := by simp only [v, Units.coe_prod]
    rw [hv, mul_comm]
    exact hh
  have hfunit :
      etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g' i) (hg' i) =
        Units.map (X.germToFunctionField cX.U).hom v *
          (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i)) := by
    rw [regularEquationRationalUnits_prod_unit_change cX.U g g' hg hg' u hu]
    exact mul_left_comm _ _ _
  have he : ∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
      moduleOverFrameCoefficient M V e' W hWV s =
        Y.presheaf.map (homOfLE hWV).op (i.app cX.U ↑v) *
          moduleOverFrameCoefficient M V e W hWV s := by
    intro W hWV s
    exact cartierPullbackFrameCoefficient_unit_equation_change (KX + ∑ i, E i) i cX.U
      _ _ (canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq)
      (canonicalPlusCartierSum_local_equation cX₀ hX cX E g' hg' hEq') v hfunit W hWV s
  let Φ := moduleOverFrameWeightedIso M KY.sheaf V e d a
  have hΦ : moduleOverFrameWeightedIso M KY.sheaf V e' d a' = Φ :=
    moduleWeightedFrameIso_cancel_source_change M KY.sheaf V e e' d a a'
      (i.app cX.U ↑v) hscalar he
  dsimp only
  refine ⟨R, R', a, a', Φ, hR, hR', ha, ha', rfl, hΦ.symm, ?_⟩
  intro W hWV s
  constructor
  · exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e d a W hWV s
  · rw [← hΦ]
    exact moduleOverFrameWeightedIso_coefficient M KY.sheaf V e' d a' W hWV s

end MixedFujita
