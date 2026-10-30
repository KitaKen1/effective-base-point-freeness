/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierResidueRestrictions

/-! 実局所標準随伴層同型の任意affine細分での全部分開一致。 check-286：実スキーム射の自然性から、切断環と任意affine制限の可換図式および両経路で同一のスカラー作用を内部証明。実etale座標の最高次微分形式の正確な制限則を証明。実有効Cartier切断の二つの正規化留数を、元の開と任意の非空affine部分開の実商環から内部構成し、その自然性とframe単元が元の単元の実制限そのものであることを証明。元の標準因子と切断方程式の積の厳密な制限不変性も証明。元のi^*O(K_X+D)からO(K_Y)への実局所標準随伴層同型を両開で内部構成し、空開を含む全ての更なる部分開で写像が一致することを証明。共通affine細分上での任意二チャートの比較、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

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


/-- Actual weighted Cartier pullback sheaf isomorphisms restrict using the
restricted SAME unit, on every further subopen, including empty opens. -/
theorem cartierWeightedPullbackIso_affine_restriction
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (i : Y ⟶ X)
    (D : CartierDivisor X) (E : CartierDivisor Y)
    (U V : X.Opens) [Nonempty U] [Nonempty V]
    [Nonempty (i ⁻¹ᵁ U)] [Nonempty (i ⁻¹ᵁ V)] (hVU : V ≤ U)
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (g : Y.functionFieldˣ) (hg : rationalUnitClass Y (i ⁻¹ᵁ U) (Additive.ofMul g) = E |_ (i ⁻¹ᵁ U))
    (a : Γ(Y, i ⁻¹ᵁ U)ˣ) :
    let hpre : i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U := fun _x hx => hVU hx
    let M := (Scheme.Modules.pullback i).obj D.sheaf
    let eU := moduleRestrictFrameOverIso M (i ⁻¹ᵁ U) (cartierPullbackLocalFrameIso D i U f hf)
    let eV := moduleRestrictFrameOverIso M (i ⁻¹ᵁ V)
      (cartierPullbackLocalFrameIso D i V f (CartierDivisor.rationalUnitClass_eq_of_le hVU hf))
    let dU := cartierOpenFrameIso E (i ⁻¹ᵁ U) g hg
    let dV := cartierOpenFrameIso E (i ⁻¹ᵁ V) g (CartierDivisor.rationalUnitClass_eq_of_le hpre hg)
    let aV := Units.map (Y.presheaf.map (homOfLE hpre).op).hom.toMonoidHom a
    ∀ (W : Y.Opens) (hWV : W ≤ i ⁻¹ᵁ V) (s : Γ(M, W)),
      (moduleOverFrameWeightedIso M E.sheaf (i ⁻¹ᵁ V) eV dV aV).hom.val.app
          (op (Over.mk (homOfLE hWV))) s =
        (moduleOverFrameWeightedIso M E.sheaf (i ⁻¹ᵁ U) eU dU a).hom.val.app
          (op (Over.mk (homOfLE (hWV.trans hpre)))) s := by
  let hpre : i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U := fun _x hx => hVU hx
  let M := (Scheme.Modules.pullback i).obj D.sheaf
  let eU := moduleRestrictFrameOverIso M (i ⁻¹ᵁ U) (cartierPullbackLocalFrameIso D i U f hf)
  let eV := moduleRestrictFrameOverIso M (i ⁻¹ᵁ V)
    (cartierPullbackLocalFrameIso D i V f (CartierDivisor.rationalUnitClass_eq_of_le hVU hf))
  let dU := cartierOpenFrameIso E (i ⁻¹ᵁ U) g hg
  let dV := cartierOpenFrameIso E (i ⁻¹ᵁ V) g (CartierDivisor.rationalUnitClass_eq_of_le hpre hg)
  let aV := Units.map (Y.presheaf.map (homOfLE hpre).op).hom.toMonoidHom a
  dsimp only
  intro W hWV s
  apply (moduleOverFrameCoefficient E.sheaf (i ⁻¹ᵁ U) dU W (hWV.trans hpre)).injective
  rw [← cartierOpenFrameCoefficient_affine_restriction E (i ⁻¹ᵁ U) (i ⁻¹ᵁ V) hpre g hg]
  rw [moduleOverFrameWeightedIso_coefficient, moduleOverFrameWeightedIso_coefficient,
    cartierPullbackFrameCoefficient_affine_restriction D i U V hVU f hf W hWV s]
  congr 1
  change Y.presheaf.map (homOfLE hWV).op
    (Y.presheaf.map (homOfLE hpre).op (a : Γ(Y, i ⁻¹ᵁ U))) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl


/-- The actual canonical-plus-cut rational equation is unchanged on affine
refinements, with the actual restricted regular equation. -/
theorem canonicalPlusCartierEquation_affine_restriction
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n : ℕ}
    (c₀ c : EtaleChart K X n) (W : X.affineOpens) [Nonempty W.1] (hWU : W.1 ≤ c.U)
    (g : Γ(X, c.U)) (hg : g ≠ 0)
    (hgW : X.presheaf.map (homOfLE hWU).op g ≠ 0) :
    etaleChartCanonicalEquation c₀ (etaleChartAffineRestriction c W hWU) *
        regularEquationRationalUnit X W.1 (X.presheaf.map (homOfLE hWU).op g) hgW =
      etaleChartCanonicalEquation c₀ c * regularEquationRationalUnit X c.U g hg := by
  rw [etaleChartAffineRestriction_canonical_equation]
  congr 1
  exact Units.ext (germToFunctionField_restrict X hWU g)


/-- Original Cartier-cut geometry constructs normalized residues and actual
local canonical-adjunction SHEAF isomorphisms on nested affine opens whose
maps agree on EVERY further subopen. All square scalar towers, residue
normalizations and frame restriction laws are derived internally. -/
theorem smooth_effectiveCartier_local_adjunction_affine_restriction
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
    (hy : y.toRingHom.FormallyEtale)
    (cX₀ : EtaleChart K X (1 + r))
    (hX : iSup (fun c : EtaleChart K X (1 + r) => c.U) = ⊤)
    (cY₀ : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r)
    (hY : iSup (fun c : EtaleChart K (effectiveCartierIdealSheaf D hD).subscheme r => c.U) = ⊤) :
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
    let cY : EtaleChart K Y r :=
      { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
        coords := y, formallyEtale := hy }
    let KX := canonicalDivisor (1 + r) cX₀ hX
    let KY := canonicalDivisor r cY₀ hY
    let M := (Scheme.Modules.pullback i).obj (KX + D).sheaf
    let fX := etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg
    let hfX := canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq
    let fY := etaleChartCanonicalEquation cY₀ cY
    let hfY := (canonicalDivisor_restrict cY₀ hY cY).symm
    let eU := moduleRestrictFrameOverIso M V
      (cartierPullbackLocalFrameIso (KX + D) i cX.U fX hfX)
    let eW := moduleRestrictFrameOverIso M V'
      (cartierPullbackLocalFrameIso (KX + D) i W.1 fX
        (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX))
    let dU := cartierOpenFrameIso KY V fY hfY
    let dW := cartierOpenFrameIso KY V' fY (CartierDivisor.rationalUnitClass_eq_of_le hpre hfY)
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
        exteriorDifferentialMap K K B C r (R w)) ∧
      (∀ (Z : Y.Opens) (hZ : Z ≤ V') (s : Γ(M, Z)),
        (moduleOverFrameWeightedIso M KY.sheaf V' eW dW
            (Units.map etaB.toRingHom.toMonoidHom a)).hom.val.app
              (op (Over.mk (homOfLE hZ))) s =
          (moduleOverFrameWeightedIso M KY.sheaf V eU dU a).hom.val.app
            (op (Over.mk (homOfLE (hZ.trans hpre)))) s) := by
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
  let cY : EtaleChart K Y r :=
    { U := V, isAffine := cX.isAffine.preimage i, nonempty := inferInstance,
      coords := y, formallyEtale := hy }
  let KX := canonicalDivisor (1 + r) cX₀ hX
  let KY := canonicalDivisor r cY₀ hY
  let M := (Scheme.Modules.pullback i).obj (KX + D).sheaf
  let fX := etaleChartCanonicalEquation cX₀ cX * regularEquationRationalUnit X cX.U g hg
  let hfX := canonicalPlusCartier_local_equation cX₀ hX cX D g hg hEq
  let fY := etaleChartCanonicalEquation cY₀ cY
  let hfY := (canonicalDivisor_restrict cY₀ hY cY).symm
  let eU := moduleRestrictFrameOverIso M V
    (cartierPullbackLocalFrameIso (KX + D) i cX.U fX hfX)
  let eW := moduleRestrictFrameOverIso M V'
    (cartierPullbackLocalFrameIso (KX + D) i W.1 fX
      (CartierDivisor.rationalUnitClass_eq_of_le hWU hfX))
  let dU := cartierOpenFrameIso KY V fY hfY
  let dW := cartierOpenFrameIso KY V' fY (CartierDivisor.rationalUnitClass_eq_of_le hpre hfY)
  dsimp only
  obtain ⟨R, a, R', hR, ha, hR', ha', hnat⟩ :=
    smooth_effectiveCartier_residue_affine_restriction D hD r cX g hg hEq W hWU y hy
  refine ⟨R, a, R', hR, ha, hR', ha', hnat, ?_⟩
  exact cartierWeightedPullbackIso_affine_restriction i (KX + D) KY cX.U W.1 hWU
    fX hfX fY hfY a

end MixedFujita
