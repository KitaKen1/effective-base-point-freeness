/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierResidueRestrictionSquares

/-! 実Cartier切断の両正規化留数と制限frame単元の内部構成。 check-286：実スキーム射の自然性から、切断環と任意affine制限の可換図式および両経路で同一のスカラー作用を内部証明。実etale座標の最高次微分形式の正確な制限則を証明。実有効Cartier切断の二つの正規化留数を、元の開と任意の非空affine部分開の実商環から内部構成し、その自然性とframe単元が元の単元の実制限そのものであることを証明。元の標準因子と切断方程式の積の厳密な制限不変性も証明。元のi^*O(K_X+D)からO(K_Y)への実局所標準随伴層同型を両開で内部構成し、空開を含む全ての更なる部分開で写像が一致することを証明。共通affine細分上での任意二チャートの比較、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
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


/-- Actual Cartier-cut restriction internally constructs BOTH normalized residues
and proves exact restriction of the canonical-frame unit. No square, tower,
residue, restriction law or unit comparison is assumed. -/
theorem smooth_effectiveCartier_residue_affine_restriction
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (hD : D.IsEffective)
    [(effectiveCartierIdealSheaf D hD).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf D hD).subschemeι.IsOver (Spec (CommRingCat.of K))]
    [IsIntegral (effectiveCartierIdealSheaf D hD).subscheme]
    (r : ℕ) (cX : EtaleChart K X (1 + r))
    (g : Γ(X, cX.U)) (hg : g ≠ 0)
    (hEq : rationalUnitClass X cX.U
      (Additive.ofMul (regularEquationRationalUnit X cX.U g hg)) = D |_ cX.U)
    (W : X.affineOpens) [Nonempty W.1] (hWU : W.1 ≤ cX.U)
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ cX.U)]
    [Nonempty ((effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ W.1)]
    (y : MvPolynomial (Fin r) K →ₐ[K]
      Γ((effectiveCartierIdealSheaf D hD).subscheme,
        (effectiveCartierIdealSheaf D hD).subschemeι ⁻¹ᵁ cX.U))
    (hy : y.toRingHom.FormallyEtale) :
    let I := effectiveCartierIdealSheaf D hD
    let Y := I.subscheme
    let i := I.subschemeι
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
    ∃ (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ)
        (R' : (C ⊗[S] (⋀[S]^(1 + r) Ω[S⁄K])) ≃ₗ[C] ⋀[C]^r Ω[C⁄K]),
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K A g) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
          (a : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) ∧
      (∀ z : Fin r → Ω[S⁄K],
        R' ((1 : C) ⊗ₜ[S] exteriorPower.ιMulti S (1 + r)
          (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D K S (etaA g)) z)) =
            exteriorPower.ιMulti C r (KaehlerDifferential.map K K S C ∘ z)) ∧
      R' ((1 : C) ⊗ₜ[S] exteriorPower.ιMulti S (1 + r)
        (etaleCoordinateBasis xS hxS)) =
          etaB (a : B) • exteriorPower.ιMulti C r (etaleCoordinateBasis yC hyC) ∧
      (∀ w, R' (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) (1 + r) w) =
        exteriorDifferentialMap K K B C r (R w)) := by
  let I := effectiveCartierIdealSheaf D hD
  let Y := I.subscheme
  let i := I.subschemeι
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
  let : Algebra.FormallySmooth K A := formallySmooth_of_etale_coordinates cX.coords cX.formallyEtale
  let : Algebra.FormallySmooth K B := formallySmooth_of_etale_coordinates y hy
  let : Algebra.FormallySmooth K S := formallySmooth_of_etale_coordinates xS hxS
  let : Algebra.FormallySmooth K C := formallySmooth_of_etale_coordinates yC hyC
  obtain ⟨hreg, hsurj, hker⟩ := effectiveCartier_affine_principal_quotient_data D hD
    ⟨cX.U, cX.isAffine⟩ g hg hEq
  obtain ⟨hgS, hEqS⟩ := regularEquation_restrict D hWU g hg hEq
  obtain ⟨hregS, hsurjS, hkerS⟩ := effectiveCartier_affine_principal_quotient_data D hD
    W (etaA g) hgS hEqS
  obtain ⟨R, _, hR, a, ha⟩ := smooth_principal_quotient_pulled_canonical_residue_frame
    (K := K) (A := A) (B := B) g hreg hsurj hker r
      (etaleCoordinateBasis cX.coords cX.formallyEtale) (etaleCoordinateBasis y hy)
  obtain ⟨R', _, hR', _⟩ := smooth_principal_quotient_pulled_canonical_residue_frame
    (K := K) (A := S) (B := C) (etaA g) hregS hsurjS hkerS r
      (etaleCoordinateBasis xS hxS) (etaleCoordinateBasis yC hyC)
  have hnat := pure_pulled_canonical_residue_chart_naturality
    (K := K) (A := A) (B := B) (S := S) (C := C) g hsurj r R R' hR hR'
  have hxs : exteriorDifferentialMap K K A S (1 + r)
      (exteriorPower.ιMulti A (1 + r) (etaleCoordinateBasis cX.coords cX.formallyEtale)) =
        exteriorPower.ιMulti S (1 + r) (etaleCoordinateBasis xS hxS) :=
    exteriorDifferentialMap_etaleCoordinateBasis_comp cX.coords cX.formallyEtale hxS
  have hys : exteriorDifferentialMap K K B C r
      (exteriorPower.ιMulti B r (etaleCoordinateBasis y hy)) =
        exteriorPower.ιMulti C r (etaleCoordinateBasis yC hyC) :=
    exteriorDifferentialMap_etaleCoordinateBasis_comp y hy hyC
  refine ⟨R, a, R', hR, ha, hR', ?_, hnat⟩
  have h := hnat ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
    (etaleCoordinateBasis cX.coords cX.formallyEtale))
  rw [pulledCanonicalChartChange_tmul, map_one, one_smul, hxs, ha, map_smul, hys] at h
  change _ = algebraMap B C (a : B) • exteriorPower.ιMulti C r (etaleCoordinateBasis yC hyC)
  rw [IsScalarTower.algebraMap_smul]
  exact h

end MixedFujita
