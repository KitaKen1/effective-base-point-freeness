/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentEquationIndependence

/-! 任意affine細分の元Cartier和方程式・両実留数と制限単元。 check-295：固定実成分の任意affine細分について、実制限環図式・両経路の同一スカラー作用・制限方程式を元スキーム射から内部供給し、任意余次元の両純正規化留数、その実チャート写像自然性、frame単元が元単元の実制限そのものであることを証明。元K_X+ΣE_iの積有理局所方程式が実affine制限で厳密に不変であることを証明し、元と細分側の実局所標準層同型を構成して、空開を含む全ての更なる部分開で写像が一致することを証明。固定成分随伴チャートを元SNC／Cartier方程式データと切断包含のみから定義し、対象エタール座標・源対象frame・選択実局所同型を内部構成。選択同型の純留数／frame単元による正規化仕様と、任意の独立な純正規化留数・単元から同じ選択同型になる一意性を証明し、元SNC幾何からこの固定成分チャート族の全点被覆も構成。選択済み同型の座標／方程式／affine比較への接続、任意二重なり一致と大域SNC随伴、数値随伴は残る。 -/

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


/-- The actual original canonical-plus-ALL-cuts product rational equation
is strictly unchanged on affine refinements with actual restricted equations. -/
theorem canonicalPlusCartierSumEquation_affine_restriction
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n m : ℕ}
    (c₀ c : EtaleChart K X n) (W : X.affineOpens) [Nonempty W.1] (hWU : W.1 ≤ c.U)
    (g : Fin m → Γ(X, c.U)) (hg : ∀ k, g k ≠ 0)
    (hgW : ∀ k, X.presheaf.map (homOfLE hWU).op (g k) ≠ 0) :
    etaleChartCanonicalEquation c₀ (etaleChartAffineRestriction c W hWU) *
        (∏ k, regularEquationRationalUnit X W.1 (X.presheaf.map (homOfLE hWU).op (g k)) (hgW k)) =
      etaleChartCanonicalEquation c₀ c * (∏ k, regularEquationRationalUnit X c.U (g k) (hg k)) := by
  rw [etaleChartAffineRestriction_canonical_equation]
  congr 1
  exact Finset.prod_congr rfl fun k _hk => Units.ext (germToFunctionField_restrict X hWU (g k))


/-- Actual Cartier-cut restriction internally constructs BOTH normalized residues
and proves exact restriction of the canonical-frame unit. No square, tower,
residue, restriction law or unit comparison is assumed. -/
theorem snc_component_residue_affine_restriction
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    (hclosed : IsClosed (U : Set (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme))
    (E : Fin m → CartierDivisor X) (hE : ∀ k, (E k).IsEffective)
    (hI : ∀ k, effectiveCartierIdealSheaf (E k) (hE k) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X)) (cX : EtaleChart K X (m + r))
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart cX ξ (fun k => some (τ k)))
    (hcut : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ cX.U ≤ U)
    (g : Fin m → Γ(X, cX.U)) (hg : ∀ k, g k ≠ 0)
    (hEq : ∀ k, rationalUnitClass X cX.U
      (Additive.ofMul (regularEquationRationalUnit X cX.U (g k) (hg k))) = E k |_ cX.U)
    (W : X.affineOpens) [Nonempty W.1] (hWU : W.1 ≤ cX.U)
    [Nonempty ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U)]
    [Nonempty ((U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ W.1)]
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ(U,
        (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι) ⁻¹ᵁ cX.U))
    (hy : y.toRingHom.FormallyEtale) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let Y : Scheme := U
    let i := U.ι ≫ I.subschemeι
    let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
      (by rw [Scheme.Opens.range_ι]; exact hclosed)
    let V := i ⁻¹ᵁ cX.U
    let V' := i ⁻¹ᵁ W.1
    let hpre : V' ≤ V := fun _x hx => hWU hx
    let A := Γ(X, cX.U)
    let B := Γ(Y, V)
    let S := Γ(X, W.1)
    let C := Γ(Y, V')
    let etaA : A →ₐ[K] S := sectionOpenRestrictionAlgHom hWU
    let etaB : B →ₐ[K] C := sectionOpenRestrictionAlgHom hpre
    let : Algebra A B := (i.app cX.U).hom.toAlgebra
    let : Algebra A S := etaA.toRingHom.toAlgebra
    let : Algebra B C := etaB.toRingHom.toAlgebra
    let : Algebra S C := (i.app W.1).hom.toAlgebra
    let : Algebra A C := (etaB.toRingHom.comp (i.app cX.U).hom).toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
    let : IsScalarTower K A S := IsScalarTower.of_algebraMap_eq fun k => (etaA.commutes k).symm
    let : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq fun k => (etaB.commutes k).symm
    let : IsScalarTower K S C := schemeApp_base_scalar_tower i W.1
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : IsScalarTower A S C := schemeApp_openRestriction_scalar_tower i hWU
    let : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq fun k =>
      (etaB.commutes k).symm.trans
        (congrArg etaB (Scheme.Modules.app_baseRingToStructurePresheaf (R := K) i cX.U k).symm)
    let xS := etaA.comp cX.coords
    let hxS : xS.toRingHom.FormallyEtale :=
      (etaleChartAffineRestriction cX W hWU).formallyEtale
    let yC := etaB.comp y
    let hyC : yC.toRingHom.FormallyEtale := RingHom.FormallyEtale.comp hy
      (affineOpenRestriction_formallyEtale ⟨V, cX.isAffine.preimage i⟩ ⟨V', W.2.preimage i⟩ hpre)
    ∃ (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ)
        (R' : (C ⊗[S] (⋀[S]^(m + r) Ω[S⁄K])) ≃ₗ[C] ⋀[C]^r Ω[C⁄K]),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun k : Fin m => KaehlerDifferential.D K A (g k)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      (∀ z : Fin r → Ω[S⁄K],
        R' ((1 : C) ⊗ₜ[S] exteriorPower.ιMulti S (m + r)
          (Fin.append (fun k : Fin m => KaehlerDifferential.D K S (etaA (g k))) z)) =
            exteriorPower.ιMulti C r (KaehlerDifferential.map K K S C ∘ z)) ∧
      R' ((1 : C) ⊗ₜ[S] exteriorPower.ιMulti S (m + r)
        (etaleCoordinateBasis xS hxS)) =
          etaB (a : B) • exteriorPower.ιMulti C r (etaleCoordinateBasis yC hyC) ∧
      (∀ w, R' (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) (m + r) w) =
        exteriorDifferentialMap K K B C r (R w)) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let Y : Scheme := U
  let i := U.ι ≫ I.subschemeι
  let : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι
    (by rw [Scheme.Opens.range_ι]; exact hclosed)
  let V := i ⁻¹ᵁ cX.U
  let V' := i ⁻¹ᵁ W.1
  let hpre : V' ≤ V := fun _x hx => hWU hx
  let A := Γ(X, cX.U)
  let B := Γ(Y, V)
  let S := Γ(X, W.1)
  let C := Γ(Y, V')
  let etaA : A →ₐ[K] S := sectionOpenRestrictionAlgHom hWU
  let etaB : B →ₐ[K] C := sectionOpenRestrictionAlgHom hpre
  let : Algebra A B := (i.app cX.U).hom.toAlgebra
  let : Algebra A S := etaA.toRingHom.toAlgebra
  let : Algebra B C := etaB.toRingHom.toAlgebra
  let : Algebra S C := (i.app W.1).hom.toAlgebra
  let : Algebra A C := (etaB.toRingHom.comp (i.app cX.U).hom).toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower i cX.U
  let : IsScalarTower K A S := IsScalarTower.of_algebraMap_eq fun k => (etaA.commutes k).symm
  let : IsScalarTower K B C := IsScalarTower.of_algebraMap_eq fun k => (etaB.commutes k).symm
  let : IsScalarTower K S C := schemeApp_base_scalar_tower i W.1
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A S C := schemeApp_openRestriction_scalar_tower i hWU
  let : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq fun k =>
    (etaB.commutes k).symm.trans
      (congrArg etaB (Scheme.Modules.app_baseRingToStructurePresheaf (R := K) i cX.U k).symm)
  let xS := etaA.comp cX.coords
  let hxS : xS.toRingHom.FormallyEtale :=
    (etaleChartAffineRestriction cX W hWU).formallyEtale
  let yC := etaB.comp y
  let hyC : yC.toRingHom.FormallyEtale := RingHom.FormallyEtale.comp hy
    (affineOpenRestriction_formallyEtale ⟨V, cX.isAffine.preimage i⟩ ⟨V', W.2.preimage i⟩ hpre)
  dsimp only
  obtain ⟨hsurj, _hker⟩ := snc_component_affine_quotient_data cX ξ τ hc U hcut
  choose hgW hEqW using fun k => regularEquation_restrict (E k) hWU (g k) (hg k) (hEq k)
  let cW := etaleChartAffineRestriction cX W hWU
  have hcW : IsSNCChart cW ξ (fun k => some (τ k)) := isSNCChart_affineRestriction cX hc W hWU
  have hcutW : I.subschemeι ⁻¹ᵁ W.1 ≤ U := (I.subschemeι.preimage_mono hWU).trans hcut
  obtain ⟨R, a, hR, ha⟩ := snc_component_cartier_sum_residue_canonical_frame
    cX ξ τ hc U hcut E hE hI g hg hEq y hy
  obtain ⟨R', _a', hR', _ha'⟩ := snc_component_cartier_sum_residue_canonical_frame
    cW ξ τ hcW U hcutW E hE hI (fun k => etaA (g k)) hgW hEqW yC hyC
  have hnat := pure_complete_intersection_residue_chart_naturality
    (K := K) (A := A) (B := B) (S := S) (C := C) m g hsurj r R R' hR hR'
  have hxs : exteriorDifferentialMap K K A S (m + r)
      (exteriorPower.ιMulti A (m + r) (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
        exteriorPower.ιMulti S (m + r) (etaleCoordinateBasis xS hxS) :=
    exteriorDifferentialMap_etaleCoordinateBasis_comp cX.coords cX.formallyEtale hxS
  have hys : exteriorDifferentialMap K K B C r
      (exteriorPower.ιMulti B r (etaleCoordinateBasis y hy)) =
        exteriorPower.ιMulti C r (etaleCoordinateBasis yC hyC) :=
    exteriorDifferentialMap_etaleCoordinateBasis_comp y hy hyC
  refine ⟨R, a, R', hR, ha, hR', ?_, hnat⟩
  have h := hnat ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
    (etaleCoordinateBasis cX.coords cX.formallyEtale))
  rw [pulledCanonicalChartChange_tmul, map_one, one_smul, hxs, ha] at h
  have hsc : exteriorDifferentialMap K K B C r
      ((a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy)) =
        algebraMap B C (a : B) • exteriorDifferentialMap K K B C r
          (exteriorPower.ιMulti B r (etaleCoordinateBasis y hy)) := by
    rw [map_smul, IsScalarTower.algebraMap_smul]
  rw [hsc, hys] at h
  change _ = algebraMap B C (a : B) • exteriorPower.ιMulti C r (etaleCoordinateBasis yC hyC)
  exact h

end MixedFujita
