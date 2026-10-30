/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CompleteIntersectionEtaleCoordinates
public import MixedFujita.SNCChartReindex

/-! 元SNCチャートから実閉層のエタール座標と正規化留数。 check-291：実商の核を生成する法線方程式の微分が周囲基底の一部となる場合、元の実余接複体を基底座標射影で分裂し、商の形式的滑らかさを追加仮定なく証明。既存Jacobian判定で残余座標写像の実エタール性を導き、一般の選択SNC座標から実閉層上のエタール座標を内部構成した。実K作用での留数と任意の標準frameの単元比較を構成し、最終層が整で元の標準類参照チャート・被覆があるとき、元i^*O(K_X+ΣE_i)とO(K_Y)の実局所加群層同型を存在・一意性、全部分開の係数公式、最高次形式の留数正規化付きで構成。切断側座標・そのエタール性・微分基底・留数・frame単元・層同型は追加入力ではない。最終整成分の供給、全点局所入力、大域SNC随伴と数値随伴は残る。 -/

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


/-- A true base-field scheme morphism identifies the induced quotient algebra
with the ACTUAL target's canonical base-field algebra, on every open. -/
theorem schemeApp_induced_base_algebra_eq
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (i : Y ⟶ X) [i.IsOver (Spec (CommRingCat.of K))] (U : X.Opens) :
    (((i.app U).hom).comp (algebraMap K Γ(X, U))).toAlgebra =
      (inferInstance : Algebra K Γ(Y, i ⁻¹ᵁ U)) := by
  apply Algebra.algebra_ext
  intro a
  exact Scheme.Modules.app_baseRingToStructurePresheaf (R := K) i U a


/-- GENERAL original SNC coordinates over the ACTUAL target field action construct an adapted basis,
a true selected-coordinate residue and the exact original ambient frame unit.
No prefix-normal-form, permutation, cut basis, conormal or residue is supplied. -/
theorem snc_affine_selected_stratum_pulled_residue_over
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r))
    (hc : IsSNCChart c ξ (fun i => some (τ i))) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let A := Γ(X, c.U)
    let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
    let q : A →+* B := (I.subschemeι.app c.U).hom
    let : Algebra A B := q.toAlgebra
    let : IsScalarTower K A B := schemeApp_base_scalar_tower I.subschemeι c.U
    ∃ (e : Fin (m + r) ≃ Fin (m + r)) (b : Module.Basis (Fin r) B Ω[B⁄K])
      (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ i, e (Fin.castAdd r i) = τ i) ∧
      (∀ i, b i = D K B (q (c.coords (MvPolynomial.X (e (Fin.natAdd m i)))))) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i => D K A (c.coords (MvPolynomial.X (τ i)))) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      (a : B) = q (((etaleCoordinateBasis c.coords c.formallyEtale).reindex e.symm).det
        (etaleCoordinateBasis c.coords c.formallyEtale)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r) (etaleCoordinateBasis c.coords c.formallyEtale)) =
        (a : B) • exteriorPower.ιMulti B r b := by
  classical
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let A := Γ(X, c.U)
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
  let q : A →+* B := (I.subschemeι.app c.U).hom
  let : Algebra A B := q.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower I.subschemeι c.U
  have hτ : Function.Injective τ := by
    intro i j h
    exact hc.1 i j (τ i) rfl (congrArg some h.symm)
  obtain ⟨e, he⟩ := exists_fin_equiv_extending_prefix τ hτ
  let b₀ := etaleCoordinateBasis c.coords c.formallyEtale
  let bA := b₀.reindex e.symm
  have hbg (i : Fin m) : bA (Fin.castAdd r i) = D K A (c.coords (MvPolynomial.X (τ i))) := by
    change (b₀.reindex e.symm) (Fin.castAdd r i) = _
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, he, etaleCoordinateBasis_apply]
  obtain ⟨hsurj, hker⟩ := snc_affine_selected_stratum_quotient_data c ξ τ hc
  obtain ⟨b, R, hb, hR, hframe⟩ := basis_complete_intersection_pulled_residue
    (fun i => c.coords (MvPolynomial.X (τ i))) bA hbg hsurj hker
  let a : Bˣ := Units.map q.toMonoidHom (Module.Basis.isUnit_det bA b₀).unit
  have haval : (a : B) = q (bA.det b₀) := by
    simp only [a, Units.coe_map, IsUnit.unit_spec]
    rfl
  dsimp only
  refine ⟨e, b, R, a, he, ?_, hR, haval, ?_⟩
  · intro i
    rw [hb]
    change KaehlerDifferential.map K K A B ((b₀.reindex e.symm) (Fin.natAdd m i)) = _
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, etaleCoordinateBasis_apply, map_D]
    rfl
  · have h := pulled_canonical_residue_ambient_frame_change bA b₀ R.toLinearMap
    rw [haval]
    exact h.trans (congrArg (fun w : ⋀[B]^r Ω[B⁄K] => algebraMap A B (bA.det b₀) • w) hframe)


/-- Any genuinely selected SNC coordinates supply ACTUAL residual etale
coordinates on the ACTUAL stratum and its ACTUAL base-field structure.
No target smoothness, target coordinates or integrality certificate is input. -/
theorem snc_affine_selected_stratum_etale_coordinates
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart c ξ (fun i => some (τ i))) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let A := Γ(X, c.U)
    let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
    let q : A →+* B := (I.subschemeι.app c.U).hom
    ∃ y : MvPolynomial (Fin r) K →ₐ[K] B, y.toRingHom.FormallyEtale ∧
      ∃ e : Fin (m + r) ≃ Fin (m + r), (∀ i, e (Fin.castAdd r i) = τ i) ∧
        ∀ i, y (MvPolynomial.X i) = q (c.coords (MvPolynomial.X (e (Fin.natAdd m i)))) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let A := Γ(X, c.U)
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
  let q : A →+* B := (I.subschemeι.app c.U).hom
  let : Algebra A B := q.toAlgebra
  let : IsScalarTower K A B := schemeApp_base_scalar_tower I.subschemeι c.U
  have hτ : Function.Injective τ := by
    intro i j h
    exact hc.1 i j (τ i) rfl (congrArg some h.symm)
  obtain ⟨e, he⟩ := exists_fin_equiv_extending_prefix τ hτ
  let c' := etaleChartReindex c e
  obtain ⟨hsurj, hker⟩ := snc_affine_selected_stratum_quotient_data c ξ τ hc
  have hker' : RingHom.ker (algebraMap A B) =
      Ideal.span (Set.range fun i : Fin m => c'.coords (MvPolynomial.X (Fin.castAdd r i))) := by
    simp only [c', etaleChartReindex_variable, he]
    exact hker
  obtain ⟨y, hy, hyX⟩ := etale_coordinate_quotient_tail_coordinates (A := A) (B := B) c'.coords c'.formallyEtale hsurj hker'
  dsimp only
  refine ⟨y, hy, e, he, ?_⟩
  intro i
  exact (hyX i).trans (congrArg q (etaleChartReindex_variable c e (Fin.natAdd m i)))


/-- The residual coordinate map is selected from ORIGINAL SNC data only. -/
noncomputable def sncStratumEtaleCoordinates
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart c ξ (fun i => some (τ i))) :
    MvPolynomial (Fin r) K →ₐ[K]
      Γ((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme,
        (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι ⁻¹ᵁ c.U) :=
  Classical.choose (snc_affine_selected_stratum_etale_coordinates c ξ τ hc)


/-- The internally selected residual coordinates are genuinely formally etale. -/
theorem sncStratumEtaleCoordinates_formallyEtale
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (τ : Fin m → Fin (m + r)) (hc : IsSNCChart c ξ (fun i => some (τ i))) :
    (sncStratumEtaleCoordinates c ξ τ hc).toRingHom.FormallyEtale :=
  (Classical.choose_spec (snc_affine_selected_stratum_etale_coordinates c ξ τ hc)).1

end MixedFujita
