/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PureResidueChartRestrictionNaturality

/-! 実Cartier切断環の制限図式と最高次形式の制限。 check-286：実スキーム射の自然性から、切断環と任意affine制限の可換図式および両経路で同一のスカラー作用を内部証明。実etale座標の最高次微分形式の正確な制限則を証明。実有効Cartier切断の二つの正規化留数を、元の開と任意の非空affine部分開の実商環から内部構成し、その自然性とframe単元が元の単元の実制限そのものであることを証明。元の標準因子と切断方程式の積の厳密な制限不変性も証明。元のi^*O(K_X+D)からO(K_Y)への実局所標準随伴層同型を両開で内部構成し、空開を含む全ての更なる部分開で写像が一致することを証明。共通affine細分上での任意二チャートの比較、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

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


/-- The actual Cartier-cut restriction square commutes by Scheme.Hom.naturality. -/
theorem schemeApp_openRestriction_square
    {X Y : Scheme.{u}} (i : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U) :
    ((Y.presheaf.map (homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from fun _x hx => hVU hx)).op).hom).comp
        (i.app U).hom =
      (i.app V).hom.comp (X.presheaf.map (homOfLE hVU).op).hom := by
  exact congrArg (fun f : Γ(X, U) ⟶ Γ(Y, i ⁻¹ᵁ V) => f.hom)
    (i.naturality (homOfLE hVU).op).symm


/-- Both paths in the actual square induce the SAME source scalar action. -/
theorem schemeApp_openRestriction_scalar_tower
    {X Y : Scheme.{u}} (i : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U) :
    let A := Γ(X, U)
    let B := Γ(Y, i ⁻¹ᵁ U)
    let S := Γ(X, V)
    let C := Γ(Y, i ⁻¹ᵁ V)
    let etaA : A →+* S := (X.presheaf.map (homOfLE hVU).op).hom
    let etaB : B →+* C :=
      (Y.presheaf.map (homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from fun _x hx => hVU hx)).op).hom
    let : Algebra A S := etaA.toAlgebra
    let : Algebra S C := (i.app V).hom.toAlgebra
    let : Algebra A C := (etaB.comp (i.app U).hom).toAlgebra
    IsScalarTower A S C := by
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  let : Algebra Γ(X, V) Γ(Y, i ⁻¹ᵁ V) := (i.app V).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(Y, i ⁻¹ᵁ V) :=
    (((Y.presheaf.map (homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from fun _x hx => hVU hx)).op).hom).comp
      (i.app U).hom).toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun a =>
    DFunLike.congr_fun (schemeApp_openRestriction_square i hVU) a


/-- Exterior differential restriction preserves the actual coordinate wedge. -/
theorem exteriorDifferentialMap_etaleCoordinateBasis_comp
    {K A S : Type*} [Field K] [CommRing A] [CommRing S]
    [Algebra K A] [Algebra K S] [Algebra A S] [IsScalarTower K A S]
    {n : ℕ} (x : MvPolynomial (Fin n) K →ₐ[K] A)
    (hx : x.toRingHom.FormallyEtale)
    (hxS : ((IsScalarTower.toAlgHom K A S).comp x).toRingHom.FormallyEtale) :
    exteriorDifferentialMap K K A S n
        (exteriorPower.ιMulti A n (etaleCoordinateBasis x hx)) =
      exteriorPower.ιMulti S n
        (etaleCoordinateBasis ((IsScalarTower.toAlgHom K A S).comp x) hxS) := by
  change exteriorScalarMap A S _ _ (KaehlerDifferential.map K K A S) n _ = _
  rw [exteriorScalarMap_wedge]
  congr 1
  funext j
  simp only [Function.comp_apply, etaleCoordinateBasis_apply, map_D]
  rfl

end MixedFujita
