/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoordinateCompleteIntersectionResidue

/-! 順序付き完全交差純留数の一意性と任意環図式自然性。 check-289：Mathlibの基底付き完全列APIで、基底の前半を核として殺す商の実基底と注入核写像・完全性を内部構成。実商イデアルの生成元から引き戻し微分の核がdgのspanであることを、Leibnizと既存conormal完全列から証明。任意余次元のetale座標商について、商側座標・Smooth性・完全列を仮定せず、残りの座標微分から商側基底と正規化留数を構成。OAIの任意階数完全列の行列式同型を用い、正規化frame係数が厳密に1であることを証明。順序付き純dg正規化による留数の一意性と任意可換環図式での自然性も証明。元SNCチャートの選択成分が前半座標に並ぶ局所形で、実sncStratumIdealの交差イデアル・実切断環の全射と核を内部同定し、実SNC閉層上の任意余次元留数を供給。中間商環や全閉層の整性は仮定しない。SNC全体の座標並べ替え・方程式変更・大域反復随伴、数値随伴は残る。 -/

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


/-- Ordered COMPLETE INTERSECTION pure dg-prefix wedges detect maps into ANY actual B-module, including
the target of a restriction square. Differential lifts come from quotient surjectivity. -/
theorem pure_complete_intersection_residue_linear_ext
    {K A B N : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B] [AddCommGroup N] [Module B N]
    (m : ℕ) (g : Fin m → A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i : Fin m => D K A (g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (P Q : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) →ₗ[B] N)
    (hPQ : ∀ z : Fin r → Ω[A⁄K],
      P ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => D K A (g i)) z)) =
        Q ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => D K A (g i)) z))) : P = Q := by
  classical
  have hp := KaehlerDifferential.map_surjective_of_surjective K K A B hsurj
  have he : P.comp R.symm.toLinearMap = Q.comp R.symm.toLinearMap := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span B r Ω[B⁄K])
    rintro _ ⟨v, rfl⟩
    choose z hz using fun j => hp (v j)
    have hv : KaehlerDifferential.map K K A B ∘ z = v := funext hz
    rw [← hv]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hback : R.symm (exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) =
        (1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => D K A (g i)) z) := by
      apply R.injective
      rw [R.apply_symm_apply, hR]
    rw [hback]
    exact hPQ z
  apply LinearMap.ext
  intro w
  have h := LinearMap.congr_fun he (R w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, R.symm_apply_apply] using h


/-- The ordered complete-intersection pure normalization uniquely determines
the actual residue independently of all target bases and conormal splittings. -/
theorem pure_complete_intersection_residue_unique
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (m : ℕ) (g : Fin m → A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (R R' : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i : Fin m => D K A (g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (hR' : ∀ z : Fin r → Ω[A⁄K],
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i : Fin m => D K A (g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) : R = R' := by
  apply LinearEquiv.toLinearMap_injective
  exact pure_complete_intersection_residue_linear_ext m g hsurj r R hR R.toLinearMap R'.toLinearMap
    (fun z => (hR z).trans (hR' z).symm)


/-- Ordered COMPLETE INTERSECTION pure normalized residues commute with ANY compatible chart ring square.
Only actual quotient surjectivity is used, not a localization description,
chosen compatible residues, splitting, or full conormal formula. -/
theorem pure_complete_intersection_residue_chart_naturality
    {K A B S C : Type*} [CommRing K] [CommRing A] [CommRing B] [CommRing S] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K S] [Algebra K C]
    [Algebra A B] [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower K A B] [IsScalarTower K A S] [IsScalarTower K A C]
    [IsScalarTower K B C] [IsScalarTower K S C] [IsScalarTower A B C] [IsScalarTower A S C]
    (m : ℕ) (g : Fin m → A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (R' : (C ⊗[S] (⋀[S]^(m + r) Ω[S⁄K])) ≃ₗ[C] ⋀[C]^r Ω[C⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i : Fin m => D K A (g i)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (hR' : ∀ z : Fin r → Ω[S⁄K],
      R' ((1 : C) ⊗ₜ[S] exteriorPower.ιMulti S (m + r)
        (Fin.append (fun i : Fin m => D K S (algebraMap A S (g i))) z)) =
          exteriorPower.ιMulti C r (KaehlerDifferential.map K K S C ∘ z)) :
    ∀ w, R' (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) (m + r) w) =
      exteriorDifferentialMap K K B C r (R w) := by
  have hm : (R'.toLinearMap.restrictScalars B).comp
        (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) (m + r)) =
      (exteriorDifferentialMap K K B C r).comp R.toLinearMap := by
    apply pure_complete_intersection_residue_linear_ext m g hsurj r R hR
    intro z
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [pulledCanonicalChartChange_tmul, map_one, one_smul]
    change R' ((1 : C) ⊗ₜ[S] exteriorScalarMap A S _ _ (KaehlerDifferential.map K K A S) (m + r)
      (exteriorPower.ιMulti A (m + r) (Fin.append (fun i : Fin m => D K A (g i)) z))) = _
    rw [exteriorScalarMap_wedge]
    have hv : KaehlerDifferential.map K K A S ∘
        Fin.append (fun i : Fin m => D K A (g i)) z =
      Fin.append (fun i : Fin m => D K S (algebraMap A S (g i)))
        (KaehlerDifferential.map K K A S ∘ z) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Function.comp_apply, Fin.append_left, Fin.append_right, map_D]
    rw [hv, hR', hR]
    change _ = exteriorScalarMap B C _ _ (KaehlerDifferential.map K K B C) r
      (exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    rw [exteriorScalarMap_wedge]
    congr 1
    funext j
    simp only [Function.comp_apply]
    rw [OAI.ReverseLogKodaira.RelativeCanonical.differential_map_tower K A S C,
      OAI.ReverseLogKodaira.RelativeCanonical.differential_map_tower K A B C]
  intro w
  exact LinearMap.congr_fun hm w

end MixedFujita
