/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentEtaleAtlas

/-! 元SNC幾何から実整成分上の一意な局所標準層随伴。 check-293：実閉部分スキームの切断近傍全体を含む開成分では、開埋込みの実切断写像が同型となることから、成分上の実商写像の全射性と元と同じ核を内部証明。任意選択エタール座標商の実微分基底・純留数を代数APIへ一般化し、元SNC座標と実成分切断写像の合成で成分上の実エタール座標を構成。元SNC族と元Cartier方程式から、非整・非連結の全閉層の任意の実開閉成分上に残余エタール被覆を内部供給。成分上の元Cartier方程式に正規化された実留数と標準frame単元を構成し、整成分上の実j^*O(K_X+ΣE_i)とO(K_U)の局所加群層同型を一意性・全部分開係数則・最高次形式の正規化付きで構成。最後に元滑らかなNoetherian SNC幾何と元の交差点から、実整成分・実整切断近傍・実Cartier方程式・成分標準類の参照チャート・同じ局所層同型をすべて内部供給する存在定理へ接続。全閉層／中間層の整性、与えた成分・商核・対象被覆・留数・層同型は入力に置かない。重なり一致・大域SNC随伴・数値随伴は残る。 -/

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


/-- Original arbitrary-codimension SNC Cartier equations construct on an ACTUAL open component a pure
residue for the ACTUAL target base-field action and ANY genuine target etale
coordinate frame. Residue and frame unit are outputs, never certificates. -/
theorem snc_component_cartier_sum_residue_canonical_frame
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ}
    (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart c ξ (fun i => some (τ i)))
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hcut : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ c.U ≤ U)
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X))
    (g : Fin m → Γ(X, c.U)) (hg : ∀ i, g i ≠ 0)
    (hEq : ∀ i, rationalUnitClass X c.U
      (Additive.ofMul (regularEquationRationalUnit X c.U (g i) (hg i))) = E i |_ c.U)
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ(U, (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ c.U))
    (hy : y.toRingHom.FormallyEtale) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let j := U.ι ≫ I.subschemeι
    let A := Γ(X, c.U)
    let B := Γ(U, j ⁻¹ᵁ c.U)
    let : Algebra A B := (j.app c.U).hom.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower j c.U
    ∃ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i => D K A (g i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis c.coords c.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let j := U.ι ≫ I.subschemeι
  let A := Γ(X, c.U)
  let B := Γ(U, j ⁻¹ᵁ c.U)
  let q : A →+* B := (j.app c.U).hom
  let : Algebra A B := q.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower j c.U
  have hτ : Function.Injective τ := by
    intro i k h
    exact hc.1 i k (τ i) rfl (congrArg some h.symm)
  obtain ⟨hsurj, hker⟩ := snc_component_affine_quotient_data c ξ τ hc U hcut
  obtain ⟨_e, b, R, a, _he, _hb, hR, _ha, hframe⟩ := selected_etale_quotient_pulled_residue
    c.coords c.formallyEtale τ hτ hsurj hker
  obtain ⟨u, hu⟩ := snc_original_cartier_equations_units c ξ τ hc E hE hI g hg hEq
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
Only the ACTUAL final open component U is integral; the whole stratum may be disconnected/nonintegral; no intermediate-integrality, permutation,
cut differential basis, residue, frame unit or sheaf-iso certificate is input.
The genuine target etale coordinates and their etaleness are constructed internally from the original SNC chart. -/
theorem snc_component_cartier_sum_local_adjunction_iso
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
    [Nonempty ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U)]
    (cY₀ : EtaleChart K U r) :
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
    let y := sncComponentEtaleCoordinates cX ξ τ hc U
    let hy := sncComponentEtaleCoordinates_formallyEtale cX ξ τ hc U hcut
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
  let Y : Scheme := U
  let i := U.ι ≫ I.subschemeι
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  let V := i ⁻¹ᵁ cX.U
  let A := Γ(X, cX.U)
  let B := Γ(Y, V)
  let : Algebra A B := (i.app cX.U).hom.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
  let y := sncComponentEtaleCoordinates cX ξ τ hc U
  let hy := sncComponentEtaleCoordinates_formallyEtale cX ξ τ hc U hcut
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
  let d := cartierOpenFrameIso KY V (etaleChartCanonicalEquation cY₀ cY)
    (canonicalDivisor_restrict cY₀ hY cY).symm
  obtain ⟨R, a, hR, ha⟩ := snc_component_cartier_sum_residue_canonical_frame
    cX ξ τ hc U hcut E hE hI g hg hEq y hy
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


/-- ORIGINAL smooth Noetherian SNC geometry, component Cartier divisors and
an original stratum point internally construct the final INTEGRAL component,
actual canonical reference chart, actual local SHEAF adjunction and exact
normalization. No component, target atlas, residue or sheaf iso is supplied. -/
theorem snc_original_geometry_exists_component_adjunction_at
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X))
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (p : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) :
    ∃ (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
      (hint : IsIntegral U)
      (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
      (hpU : p ∈ U) (cX : EtaleChart K X (m + r)) (τ : Fin m → Fin (m + r))
      (hc : IsSNCChart cX ξ (fun i => some (τ i)))
      (hcut : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ cX.U ≤ U)
      (g : Fin m → Γ(X, cX.U)) (hg : ∀ i, g i ≠ 0)
      (hEq : ∀ i, rationalUnitClass X cX.U
        (Additive.ofMul (regularEquationRationalUnit X cX.U (g i) (hg i))) = E i |_ cX.U)
      (hp : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι p ∈ cX.U)
      (cY₀ : EtaleChart K U r),
    let : IsIntegral U := hint
    let : Nonempty ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U) :=
      ⟨⟨⟨p, hpU⟩, hp⟩⟩
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
    let y := sncComponentEtaleCoordinates cX ξ τ hc U
    let hy := sncComponentEtaleCoordinates_formallyEtale cX ξ τ hc U hcut
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
  obtain ⟨U, cX, τ, g, hg, hp, hcut, hclosed, hint, _hintcut, _hj, hc, hEq⟩ :=
    snc_stratum_exists_integral_equation_neighbourhood ξ hsnc E hE p
  have hpU : p ∈ U := hcut hp
  let : IsIntegral U := hint
  let : Nonempty ((U.ι ≫ I.subschemeι) ⁻¹ᵁ cX.U) := ⟨⟨⟨p, hpU⟩, hp⟩⟩
  have hcover := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
  have hgeneric : genericPoint U ∈ iSup (fun c : EtaleChart K U r => c.U) := by
    rw [hcover]
    trivial
  obtain ⟨cY₀, _hcY₀⟩ := Opens.mem_iSup.mp hgeneric
  refine ⟨U, hint, hclosed, hpU, cX, τ, hc, hcut, g, hg, hEq, hp, cY₀, ?_⟩
  exact snc_component_cartier_sum_local_adjunction_iso ξ hsnc U hclosed E hE hI
    cX₀ hX cX τ hc hcut g hg hEq cY₀

end MixedFujita
