/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentResidueRestrictions

/-! 任意affine細分で実局所標準層同型が全部分開上で一致。 check-295：固定実成分の任意affine細分について、実制限環図式・両経路の同一スカラー作用・制限方程式を元スキーム射から内部供給し、任意余次元の両純正規化留数、その実チャート写像自然性、frame単元が元単元の実制限そのものであることを証明。元K_X+ΣE_iの積有理局所方程式が実affine制限で厳密に不変であることを証明し、元と細分側の実局所標準層同型を構成して、空開を含む全ての更なる部分開で写像が一致することを証明。固定成分随伴チャートを元SNC／Cartier方程式データと切断包含のみから定義し、対象エタール座標・源対象frame・選択実局所同型を内部構成。選択同型の純留数／frame単元による正規化仕様と、任意の独立な純正規化留数・単元から同じ選択同型になる一意性を証明し、元SNC幾何からこの固定成分チャート族の全点被覆も構成。選択済み同型の座標／方程式／affine比較への接続、任意二重なり一致と大域SNC随伴、数値随伴は残る。 -/

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


/-- Original Cartier-cut geometry constructs normalized residues and actual
local canonical-adjunction SHEAF isomorphisms on nested affine opens whose
maps agree on EVERY further subopen. All square scalar towers, residue
normalizations and frame restriction laws are derived internally. -/
theorem snc_component_local_adjunction_affine_restriction
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Opens)
    [IsIntegral U]
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
    (hy : y.toRingHom.FormallyEtale)
    (cX₀ : EtaleChart K X (m + r))
    (hX : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K U r) :
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
    let cY : EtaleChart K Y r :=
      { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
        coords := y, formallyEtale := hy }
    let KX := canonicalDivisor (m + r) cX₀ hX
    let hY := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
    let KY := canonicalDivisor r cY₀ hY
    let M := (Scheme.Modules.pullback i).obj (KX + ∑ k, E k).sheaf
    let fX := etaleChartCanonicalEquation cX₀ cX * ∏ k, regularEquationRationalUnit X cX.U (g k) (hg k)
    let hfX := canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq
    let fY := etaleChartCanonicalEquation cY₀ cY
    let hfY := (canonicalDivisor_restrict cY₀ hY cY).symm
    let eU := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + ∑ k, E k) i cX.U fX hfX)
    let eW := moduleRestrictFrameOverIso M V'
      (cartierPullbackLocalFrameIso (KX + ∑ k, E k) i W.1 fX
        (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX))
    let dU := cartierOpenFrameIso KY V fY hfY
    let dW := cartierOpenFrameIso KY V' fY (CartierDivisor.rationalUnitClass_eq_of_le hpre hfY)
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
        exteriorDifferentialMap K K B C r (R w)) ∧
      (∀ (Z : Y.Opens) (hZ : Z ≤ V') (s : Γ(M, Z)),
        (moduleOverFrameWeightedIso M KY.sheaf V' eW dW
            (Units.map etaB.toRingHom.toMonoidHom a)).hom.val.app
              (op (Over.mk (homOfLE hZ))) s =
          (moduleOverFrameWeightedIso M KY.sheaf V eU dU a).hom.val.app
            (op (Over.mk (homOfLE (hZ.trans hpre)))) s) := by
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
  let cY : EtaleChart K Y r :=
    { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
      coords := y, formallyEtale := hy }
  let KX := canonicalDivisor (m + r) cX₀ hX
  let hY := snc_component_etaleChart_cover ξ hsnc E hE U hclosed
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + ∑ k, E k).sheaf
  let fX := etaleChartCanonicalEquation cX₀ cX * ∏ k, regularEquationRationalUnit X cX.U (g k) (hg k)
  let hfX := canonicalPlusCartierSum_local_equation cX₀ hX cX E g hg hEq
  let fY := etaleChartCanonicalEquation cY₀ cY
  let hfY := (canonicalDivisor_restrict cY₀ hY cY).symm
  let eU := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + ∑ k, E k) i cX.U fX hfX)
  let eW := moduleRestrictFrameOverIso M V'
    (cartierPullbackLocalFrameIso (KX + ∑ k, E k) i W.1 fX
      (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX))
  let dU := cartierOpenFrameIso KY V fY hfY
  let dW := cartierOpenFrameIso KY V' fY (CartierDivisor.rationalUnitClass_eq_of_le hpre hfY)
  dsimp only
  obtain ⟨R, a, R', hR, ha, hR', ha', hnat⟩ :=
    snc_component_residue_affine_restriction ξ U hclosed E hE hI cX τ hc hcut g hg hEq W hWU y hy
  refine ⟨R, a, R', hR, ha, hR', ha', hnat, ?_⟩
  exact cartierWeightedPullbackIso_affine_restriction i (KX + ∑ k, E k) KY cX.U W.1 hWU
    fX hfX fY hfY a

end MixedFujita
