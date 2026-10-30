/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierFrameRestrictionCompatibility

/-! 独立構成した純正規化留数の任意環図式自然性。 check-285：恒等スキーム射の既存etale_appLEから任意のaffine開制限の形式的etale性を証明し、特定の局所化表示を入力せず実etaleチャートを任意の非空affine部分開へ構成。実一般点座標・微分基底・元の標準Cartier方程式が厳密に不変であることを証明。同じ有理方程式の実Cartier frameを元の開から制限したものと小さい開で作ったものが空開を含む全部分開で一致することを証明。実pullback済みframe生成元と切断pullbackの制限自然性から、実Cartier pullback frameの全部分開の制限一致も内部構成。純dg正規化による写像検出を任意のB加群へ拡張し、独立に構成した純正規化留数が任意の可換な実環図式で実引き戻し標準加群のチャート変更と可換であることを証明。実Cartier局所層同型への全環図式の接続、大域貼合せ、SNC反復随伴、数値随伴は残る。 -/

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


/-- Pure ambient dg wedges detect maps into ANY actual B-module, including
the target of a restriction square. Differential lifts come from quotient surjectivity. -/
theorem pure_pulled_residue_linear_ext_to_module
    {K A B N : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B] [AddCommGroup N] [Module B N]
    (g : A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A g) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (P Q : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) →ₗ[B] N)
    (hPQ : ∀ z : Fin r → Ω[A⁄K],
      P ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => D K A g) z)) =
        Q ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => D K A g) z))) : P = Q := by
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
        (1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => D K A g) z) := by
      apply R.injective
      rw [R.apply_symm_apply, hR]
    rw [hback]
    exact hPQ z
  apply LinearMap.ext
  intro w
  have h := LinearMap.congr_fun he (R w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, R.symm_apply_apply] using h


/-- Pure normalized residues commute with ANY compatible chart ring square.
Only actual quotient surjectivity is used, not a localization description,
chosen compatible residues, splitting, or full conormal formula. -/
theorem pure_pulled_canonical_residue_chart_naturality
    {K A B S C : Type*} [CommRing K] [CommRing A] [CommRing B] [CommRing S] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K S] [Algebra K C]
    [Algebra A B] [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower K A B] [IsScalarTower K A S] [IsScalarTower K A C]
    [IsScalarTower K B C] [IsScalarTower K S C] [IsScalarTower A B C] [IsScalarTower A S C]
    (g : A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (R' : (C ⊗[S] (⋀[S]^(1 + r) Ω[S⁄K])) ≃ₗ[C] ⋀[C]^r Ω[C⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A g) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (hR' : ∀ z : Fin r → Ω[S⁄K],
      R' ((1 : C) ⊗ₜ[S] exteriorPower.ιMulti S (1 + r)
        (Fin.append (fun _ : Fin 1 => D K S (algebraMap A S g)) z)) =
          exteriorPower.ιMulti C r (KaehlerDifferential.map K K S C ∘ z)) :
    ∀ w, R' (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) (1 + r) w) =
      exteriorDifferentialMap K K B C r (R w) := by
  have hm : (R'.toLinearMap.restrictScalars B).comp
        (pulledCanonicalChartChange (K := K) (A := A) (B := B) (S := S) (C := C) (1 + r)) =
      (exteriorDifferentialMap K K B C r).comp R.toLinearMap := by
    apply pure_pulled_residue_linear_ext_to_module g hsurj r R hR
    intro z
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
    rw [pulledCanonicalChartChange_tmul, map_one, one_smul]
    change R' ((1 : C) ⊗ₜ[S] exteriorScalarMap A S _ _ (KaehlerDifferential.map K K A S) (1 + r)
      (exteriorPower.ιMulti A (1 + r) (Fin.append (fun _ : Fin 1 => D K A g) z))) = _
    rw [exteriorScalarMap_wedge]
    have hv : KaehlerDifferential.map K K A S ∘
        Fin.append (fun _ : Fin 1 => D K A g) z =
      Fin.append (fun _ : Fin 1 => D K S (algebraMap A S g))
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
