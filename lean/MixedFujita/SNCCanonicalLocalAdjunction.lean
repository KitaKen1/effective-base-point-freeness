/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCStratumEtaleCoordinates

/-! 切断側座標を内部構成する任意余次元の実局所標準層随伴。 check-291：実商の核を生成する法線方程式の微分が周囲基底の一部となる場合、元の実余接複体を基底座標射影で分裂し、商の形式的滑らかさを追加仮定なく証明。既存Jacobian判定で残余座標写像の実エタール性を導き、一般の選択SNC座標から実閉層上のエタール座標を内部構成した。実K作用での留数と任意の標準frameの単元比較を構成し、最終層が整で元の標準類参照チャート・被覆があるとき、元i^*O(K_X+ΣE_i)とO(K_Y)の実局所加群層同型を存在・一意性、全部分開の係数公式、最高次形式の留数正規化付きで構成。切断側座標・そのエタール性・微分基底・留数・frame単元・層同型は追加入力ではない。最終整成分の供給、全点局所入力、大域SNC随伴と数値随伴は残る。 -/

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


/-- Original arbitrary-codimension SNC Cartier equations construct a pure
residue for the ACTUAL target base-field action and ANY genuine target etale
coordinate frame. Residue and frame unit are outputs, never certificates. -/
theorem snc_original_cartier_sum_residue_canonical_frame
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ}
    (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart c ξ (fun i => some (τ i)))
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X))
    (g : Fin m → Γ(X, c.U)) (hg : ∀ i, g i ≠ 0)
    (hEq : ∀ i, rationalUnitClass X c.U
      (Additive.ofMul (regularEquationRationalUnit X c.U (g i) (hg i))) = E i |_ c.U)
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme,
        (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ c.U))
    (hy : y.toRingHom.FormallyEtale) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let A := Γ(X, c.U)
    let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
    let : Algebra A B := (I.subschemeι.app c.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower I.subschemeι c.U
    ∃ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i => D K A (g i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis c.coords c.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let A := Γ(X, c.U)
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
  let q : A →+* B := (I.subschemeι.app c.U).hom
  let : Algebra A B := q.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower I.subschemeι c.U
  obtain ⟨e, b, R, a, _he, _hb, hR, _ha, hframe⟩ := snc_affine_selected_stratum_pulled_residue_over c ξ τ hc
  obtain ⟨u, hu⟩ := snc_original_cartier_equations_units c ξ τ hc E hE hI g hg hEq
  obtain ⟨_hsurj, hker⟩ := snc_affine_selected_stratum_quotient_data c ξ τ hc
  have hzero (i : Fin m) : algebraMap A B (c.coords (MvPolynomial.X (τ i))) = 0 :=
    RingHom.mem_ker.mp (hker ▸ Ideal.subset_span (Set.mem_range_self i))
  let v : Bˣ := Units.map q.toMonoidHom (∏ i, u i)
  let R' : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K] :=
    R.trans (LinearEquiv.smulOfUnit (M := ⋀[B]^r Ω[B⁄K]) v⁻¹)
  have hv : (v : B) = algebraMap A B (∏ i, (u i : A)) := by
    simp only [v, Units.coe_map, Units.coe_prod]
    rfl
  have hR' (z : Fin r → Ω[A⁄K]) :
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i => D K A (g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z) := by
      change (↑v⁻¹ : B) • R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i => D K A (g i)) z)) = _
      have hnormal : (fun i => D K A (g i)) =
          (fun i => D K A ((u i : A) * c.coords (MvPolynomial.X (τ i)))) :=
        funext fun i => congrArg (D K A) (hu i)
      have hscaled : R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i => D K A (g i)) z)) =
            (v : B) • exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z) := by
        rw [hnormal, ← pulled_complete_intersection_equation_wedge_scaling m r
          (fun i => c.coords (MvPolynomial.X (τ i))) (fun i => (u i : A)) hzero
            (etaleCoordinateBasis c.coords c.formallyEtale) z, map_smul, hR]
        exact congrArg (fun t : B => t • exteriorPower.ιMulti B r
          (KaehlerDifferential.map K K A B ∘ z)) hv.symm
      have hcancel (w : ⋀[B]^r Ω[B⁄K]) : (↑v⁻¹ : B) • ((v : B) • w) = w := by
        rw [smul_smul]
        exact (congrArg (fun t : B => t • w) v.inv_val).trans (one_smul B w)
      exact (congrArg (fun w : ⋀[B]^r Ω[B⁄K] => (↑v⁻¹ : B) • w) hscaled).trans (hcancel _)
  have hframe' : R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
      (etaleCoordinateBasis c.coords c.formallyEtale)) =
        ((v⁻¹ * a : Bˣ) : B) • exteriorPower.ιMulti B r b := by
    change (↑v⁻¹ : B) • R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
      (etaleCoordinateBasis c.coords c.formallyEtale)) = _
    exact (congrArg (fun w : ⋀[B]^r Ω[B⁄K] => (↑v⁻¹ : B) • w) hframe).trans (smul_smul _ _ _)
  obtain ⟨a', _ha', hframe⟩ := pulled_canonical_residue_two_frame_transition
    (etaleCoordinateBasis c.coords c.formallyEtale)
    (etaleCoordinateBasis c.coords c.formallyEtale) b
    (etaleCoordinateBasis y hy) R'.toLinearMap (v⁻¹ * a) hframe'
  exact ⟨R', a', hR', hframe⟩


/-- ORIGINAL arbitrary-codimension SNC and Cartier-sum data internally construct
an actual UNIQUE normalized local SHEAF adjunction i^*O(K_X+SUM E_i)=O(K_Y).
Only the FINAL stratum is integral; no intermediate-integrality, permutation,
cut differential basis, residue, frame unit or sheaf-iso certificate is input.
The genuine target etale coordinates and their etaleness are constructed internally from the original SNC chart. -/
theorem snc_original_cartier_sum_local_adjunction_iso
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    [IsIntegral (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme]
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X)) (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cX : EtaleChart K X (m + r))
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart cX ξ (fun i => some (τ i)))
    (g : Fin m → Γ(X, cX.U)) (hg : ∀ i, g i ≠ 0)
    (hEq : ∀ i, rationalUnitClass X cX.U
      (Additive.ofMul (regularEquationRationalUnit X cX.U (g i) (hg i))) = E i |_ cX.U)
    [Nonempty ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ cX.U)]
    (cY₀ : EtaleChart K (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme r)
    (hY : iSup (fun c : EtaleChart K (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme r => c.U) = ⊤) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let Y := I.subscheme
    let i := I.subschemeι
    let V := i ⁻¹ᵁ cX.U
    let A := Γ(X, cX.U)
    let B := Γ(Y, V)
    let : Algebra A B := (i.app cX.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
    let y := sncStratumEtaleCoordinates cX ξ τ hc
    let hy := sncStratumEtaleCoordinates_formallyEtale cX ξ τ hc
    let cY : EtaleChart K Y r :=
      { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
        coords := y, formallyEtale := hy }
    let KX := canonicalDivisor (m + r) cX₀ hX
    let KY := canonicalDivisor r cY₀ hY
    let M := (Scheme.Modules.pullback i).obj (KX + ∑ i, E i).sheaf
    let e := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + ∑ i, E i) i cX.U
        (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i))
        (canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq))
    let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
      (canonicalDivisor_restrict cY₀ hY cY).symm
    ∃ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => KaehlerDifferential.D K A (g i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      ∃! Φ : M.over V ≅ KY.sheaf.over V,
        (∀ (W : Y.Opens) (hWV : W ≤ V) (s : Γ(M, W)),
          moduleOverFrameCoefficient KY.sheaf V d W hWV
              (Φ.hom.val.app (op (Over.mk (homOfLE hWV))) s) =
            Y.presheaf.map (homOfLE hWV).op ↑a * moduleOverFrameCoefficient M V e W hWV s) ∧
        (∀ s : Γ(M, V),
          canonicalCartierAffineFormEquiv cY₀ hY cY
              (Φ.hom.val.app (op (Over.mk (homOfLE (le_refl V)))) s) =
            moduleOverFrameCoefficient M V e V le_rfl s •
              R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
                (etaleCoordinateBasis cX.coords cX.formallyEtale))) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let Y := I.subscheme
  let i := I.subschemeι
  let V := i ⁻¹ᵁ cX.U
  let A := Γ(X, cX.U)
  let B := Γ(Y, V)
  let : Algebra A B := (i.app cX.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
  let y := sncStratumEtaleCoordinates cX ξ τ hc
  let hy := sncStratumEtaleCoordinates_formallyEtale cX ξ τ hc
  let cY : EtaleChart K Y r :=
    { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
      coords := y, formallyEtale := hy }
  let KX := canonicalDivisor (m + r) cX₀ hX
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + ∑ i, E i).sheaf
  let e := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + ∑ i, E i) i cX.U
      (etaleChartCanonicalEquation cX₀ cX * ∏ i, regularEquationRationalUnit X cX.U (g i) (hg i))
      (canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq))
  let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
    (canonicalDivisor_restrict cY₀ hY cY).symm
  obtain ⟨R, a, hR, ha⟩ := snc_original_cartier_sum_residue_canonical_frame
    cX ξ τ hc E hE hI g hg hEq y hy
  let Φ := moduleOverFrameWeightedIso M KY.sheaf V e d a
  dsimp only
  refine ⟨R, a, hR, ha, Φ, ?_, ?_⟩
  · constructor
    · exact fun W hWV s => moduleOverFrameWeightedIso_coefficient M KY.sheaf V e d a W hWV s
    · intro s
      change moduleOverFrameCoefficient KY.sheaf V d V le_rfl
          (Φ.hom.val.app (op (Over.mk (homOfLE (le_refl V)))) s) •
            exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) = _
      rw [moduleOverFrameWeightedIso_coefficient]
      rw [ha, smul_smul]
      apply congrArg (fun t : B => t • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy))
      change Y.presheaf.map (homOfLE (le_refl V)).op ↑a *
          moduleOverFrameCoefficient M V e V le_rfl s =
        moduleOverFrameCoefficient M V e V le_rfl s * ↑a
      have hres : Y.presheaf.map (homOfLE (le_refl V)).op ↑a = (a : B) :=
        Y.presheaf.map_id_apply (op V) (a : B)
      rw [hres, mul_comm]
  · intro Ψ hΨ
    exact moduleOverFrameWeightedIso_unique M KY.sheaf V e d a Ψ hΨ.1

end MixedFujita
