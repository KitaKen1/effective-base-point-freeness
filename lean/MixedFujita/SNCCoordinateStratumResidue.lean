/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CompleteIntersectionResidueNaturality
public import MixedFujita.SNCComponentCartier
public import MixedFujita.SNCStrataGenericPoints
public import MixedFujita.SNCStrataGenericSmoothness
public import MixedFujita.SNCPointDivisorFamily

/-! 実SNC閉層の商環から任意余次元正規化留数を内部構成。 check-289：Mathlibの基底付き完全列APIで、基底の前半を核として殺す商の実基底と注入核写像・完全性を内部構成。実商イデアルの生成元から引き戻し微分の核がdgのspanであることを、Leibnizと既存conormal完全列から証明。任意余次元のetale座標商について、商側座標・Smooth性・完全列を仮定せず、残りの座標微分から商側基底と正規化留数を構成。OAIの任意階数完全列の行列式同型を用い、正規化frame係数が厳密に1であることを証明。順序付き純dg正規化による留数の一意性と任意可換環図式での自然性も証明。元SNCチャートの選択成分が前半座標に並ぶ局所形で、実sncStratumIdealの交差イデアル・実切断環の全射と核を内部同定し、実SNC閉層上の任意余次元留数を供給。中間商環や全閉層の整性は仮定しない。SNC全体の座標並べ替え・方程式変更・大域反復随伴、数値随伴は残る。 -/

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


/-- The actual full SNC coordinate stratum is the actual intersection
of the original component vanishing ideals, with no component integrality input. -/
theorem snc_all_stratumIdeal_eq_iSup
    {T : Scheme.{u}} {m : ℕ} (ξ : Fin m → T) :
    sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ =
      ⨆ i : Fin m, Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T) := by
  classical
  apply le_antisymm
  · rw [sncStratumIdeal]
    apply iSup_le
    intro i
    apply iSup_le
    intro _hi
    exact le_iSup_of_le i.down le_rfl
  · apply iSup_le
    intro i
    rw [sncStratumIdeal]
    exact le_iSup_of_le (ULift.up i) (le_iSup_of_le (Finset.mem_univ _) le_rfl)


/-- Actual SNC chart equations give the full actual affine stratum quotient
kernel and surjectivity internally. No ideal-kernel certificate is supplied. -/
theorem snc_affine_coordinate_stratum_quotient_data
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    (hc : IsSNCChart c ξ (fun i => some (Fin.castAdd r i))) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let q := (I.subschemeι.app c.U).hom
    Function.Surjective q ∧ RingHom.ker q =
      Ideal.span (Set.range fun i : Fin m => c.coords (MvPolynomial.X (Fin.castAdd r i))) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  have hI : I.ideal ⟨c.U, c.isAffine⟩ =
      Ideal.span (Set.range fun i : Fin m => c.coords (MvPolynomial.X (Fin.castAdd r i))) := by
    dsimp only [I]
    rw [snc_all_stratumIdeal_eq_iSup, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    change (⨆ i : Fin m, (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X)).ideal ⟨c.U, c.isAffine⟩) = _
    simp_rw [vanishingIdeal_closure_ideal_sncChart c ξ _ hc, Option.elim_some]
    exact (Ideal.span_range_eq_iSup _).symm
  dsimp only
  refine ⟨I.subschemeι_app_surjective ⟨c.U, c.isAffine⟩, ?_⟩
  exact (I.ker_subschemeι_app ⟨c.U, c.isAffine⟩).trans hI


/-- ORIGINAL SNC chart data internally construct the actual higher-codimension
Poincare residue for the ACTUAL entire closed stratum, even if disconnected
or nonintegral. Its cut basis is the remaining coordinate differentials and
its exact canonical-frame coefficient is ONE. No cut basis, smoothness,
conormal data, regular sequence, residue or compatibility is an input. -/
theorem snc_affine_coordinate_stratum_pulled_residue
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    (hc : IsSNCChart c ξ (fun i => some (Fin.castAdd r i))) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let A := Γ(X, c.U)
    let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
    let q : A →+* B := (I.subschemeι.app c.U).hom
    let : Algebra A B := q.toAlgebra
    let : Algebra K B := (q.comp (algebraMap K A)).toAlgebra
    let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∃ (b : Module.Basis (Fin r) B Ω[B⁄K])
      (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]),
      (∀ i, b i = D K B (q (c.coords (MvPolynomial.X (Fin.natAdd m i))))) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i : Fin m => D K A (c.coords (MvPolynomial.X (Fin.castAdd r i)))) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r) (etaleCoordinateBasis c.coords c.formallyEtale)) =
        exteriorPower.ιMulti B r b := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let A := Γ(X, c.U)
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
  let q : A →+* B := (I.subschemeι.app c.U).hom
  let : Algebra A B := q.toAlgebra
  let : Algebra K B := (q.comp (algebraMap K A)).toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hsurj, hker⟩ := snc_affine_coordinate_stratum_quotient_data c ξ hc
  exact etale_coordinate_quotient_pulled_canonical_residue c.coords c.formallyEtale hsurj hker

end MixedFujita
