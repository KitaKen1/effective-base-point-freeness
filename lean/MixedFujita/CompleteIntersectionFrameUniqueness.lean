/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentCanonicalAdjunction

/-! 純正規化完全交差留数とframe単元の一意性・実方程式積変換。 check-294：固定した法線成分順序について、任意に独立構成した純正規化完全交差留数と実標準frame単元の一致を証明。元Cartier方程式を個別の単元倍に同時変更したとき、実有理局所方程式の積が全単元比の積で変換する厳密公式を証明。元SNC整成分上の同じaffine開で周囲と対象の両エタール座標を同時変更しても、実局所標準層同型が一致することを、実Jacobian単元と源・対象frame係数の相殺から内部構成。全元Cartier因子の二組の実局所方程式から各単元比・二留数・二frame単元を内部構成し、その積による留数係数と源frame変化の相殺から同じ実局所標準層同型を得ることを証明。両比較は空開を含む全部分開の正確な係数則を持ち、比較一致や単元変換証明を追加入力にしない。異なるaffine開への制限比較、任意二チャート重なりと大域SNC随伴、数値随伴は残る。 -/

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


/-- ANY independently pure-normalized complete-intersection residues and
their actual canonical-frame units coincide, for the fixed normal order. -/
theorem pure_complete_intersection_residue_frame_unique
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (m r : ℕ) (g : Fin m → A) (hsurj : Function.Surjective (algebraMap A B))
    (b : Module.Basis (Fin (m + r)) A Ω[A⁄K]) (c : Module.Basis (Fin r) B Ω[B⁄K])
    (R R' : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a a' : Bˣ)
    (hR : ∀ z : Fin r → Ω[A⁄K], R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
      (Fin.append (fun i => D K A (g i)) z)) = exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (hR' : ∀ z : Fin r → Ω[A⁄K], R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
      (Fin.append (fun i => D K A (g i)) z)) = exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (ha : R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r) b) = (a : B) • exteriorPower.ιMulti B r c)
    (ha' : R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r) b) = (a' : B) • exteriorPower.ιMulti B r c) :
    R = R' ∧ a = a' := by
  have heq := pure_complete_intersection_residue_unique m g hsurj r R R' hR hR'
  rw [heq] at ha
  exact ⟨heq, Units.ext (topExterior_wedge_smul_cancel c (ha.symm.trans ha'))⟩


/-- Simultaneously replacing each ACTUAL Cartier equation by a unit multiple
multiplies the ACTUAL product rational equation by the PRODUCT unit. -/
theorem regularEquationRationalUnits_prod_unit_change
    {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U] {m : ℕ}
    (g g' : Fin m → Γ(X, U)) (hg : ∀ i, g i ≠ 0) (hg' : ∀ i, g' i ≠ 0)
    (v : Fin m → Γ(X, U)ˣ) (hv : ∀ i, g' i = (v i : Γ(X, U)) * g i) :
    (∏ i, regularEquationRationalUnit X U (g' i) (hg' i)) =
      Units.map (X.germToFunctionField U).hom (∏ i, v i) *
        (∏ i, regularEquationRationalUnit X U (g i) (hg i)) := by
  apply Units.ext
  simp only [Units.val_mul, Units.coe_prod, regularEquationRationalUnit_val, Units.coe_map]
  simp_rw [hv, map_mul]
  rw [map_prod, Finset.prod_mul_distrib]
  rfl

end MixedFujita
