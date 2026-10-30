/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCCoordinateStratumResidue
public import Mathlib.Algebra.BigOperators.Fin

/-! 完全交差の全方程式変更に対する留数の厳密積公式。 check-290：任意の選択SNC座標を先頭へ移す実有限置換を内部構成し、元の一般IsSNCChartから実閉層の商環・微分基底・純正規化留数・元周囲frame単元を構成。先頭座標という追加仮定を除去した。全法線方程式の同時変更で留数が単元比の積により変換する厳密公式を証明。元SNC成分の実イデアルと実Cartier方程式から各単元比を内部取得し、元K_X+ΣE_iの積局所方程式と、その同じ元方程式に正規化された実SNC閉層留数を供給。切断側の基底・留数・置換・単元比や中間商環の整性は追加仮定ではない。最終成分の標準層との同型・大域SNC随伴・数値随伴は残る。 -/

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


/-- Scaling an ordered normal prefix scales its actual top wedge by the
PRODUCT of all normal scalars; arbitrary residual vectors stay unchanged. -/
theorem exteriorPower_append_prefix_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m r : ℕ) (a : Fin m → R) (v : Fin m → M) (z : Fin r → M) :
    exteriorPower.ιMulti R (m + r) (Fin.append (fun i => a i • v i) z) =
      (∏ i, a i) • exteriorPower.ιMulti R (m + r) (Fin.append v z) := by
  classical
  have hv : Fin.append (fun i => a i • v i) z =
      fun i => (Fin.append a (fun _ : Fin r => (1 : R)) i) • (Fin.append v z i) := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right, one_smul]
  rw [hv, AlternatingMap.map_smul_univ, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const_one, mul_one]


/-- Changing ALL actual quotient equations by individual scalar multiples
scales the actual pulled normal numerator by their product. -/
theorem pulled_complete_intersection_equation_wedge_scaling
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B]
    (m r : ℕ) (g a : Fin m → A) (hg : ∀ i, algebraMap A B (g i) = 0)
    (b : Module.Basis (Fin (m + r)) A Ω[A⁄K]) (z : Fin r → Ω[A⁄K]) :
    algebraMap A B (∏ i, a i) • ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i => D K A (g i)) z)) =
      (1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i => D K A (a i * g i)) z) := by
  apply (finiteFreeExteriorBaseChangeEquiv (B := B) b (m + r)).injective
  rw [map_smul, finiteFreeExteriorBaseChangeEquiv_tmul_wedge,
    finiteFreeExteriorBaseChangeEquiv_tmul_wedge, one_smul]
  have hw (v : Fin m → Ω[A⁄K]) :
      (fun i => (1 : B) ⊗ₜ[A] (Fin.append v z i)) =
        Fin.append (fun i => (1 : B) ⊗ₜ[A] v i) (fun i => (1 : B) ⊗ₜ[A] z i) := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  rw [hw, hw]
  have hnormal : (fun i => (1 : B) ⊗ₜ[A] D K A (a i * g i)) =
      fun i => algebraMap A B (a i) • ((1 : B) ⊗ₜ[A] D K A (g i)) :=
    funext fun i => quotient_equation_differential_mul (g i) (a i) (hg i)
  rw [hnormal, exteriorPower_append_prefix_smul, ← map_prod, one_smul]


/-- ANY independently normalized complete-intersection residues obey the
simultaneous equation-change law with the exact PRODUCT scalar. -/
theorem pure_complete_intersection_residue_equations_change
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (m r : ℕ) (g a : Fin m → A) (hg : ∀ i, algebraMap A B (g i) = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (b : Module.Basis (Fin (m + r)) A Ω[A⁄K])
    (R R' : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i => D K A (g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (hR' : ∀ z : Fin r → Ω[A⁄K],
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i => D K A (a i * g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) :
    ∀ w, R' (algebraMap A B (∏ i, a i) • w) = R w := by
  have hm : (algebraMap A B (∏ i, a i)) • R'.toLinearMap = R.toLinearMap := by
    apply pure_complete_intersection_residue_linear_ext m g hsurj r R hR
    intro z
    change algebraMap A B (∏ i, a i) • R' _ = R _
    rw [← map_smul, pulled_complete_intersection_equation_wedge_scaling m r g a hg b z, hR', hR]
  intro w
  have h := LinearMap.congr_fun hm w
  simpa only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul] using h

end MixedFujita
