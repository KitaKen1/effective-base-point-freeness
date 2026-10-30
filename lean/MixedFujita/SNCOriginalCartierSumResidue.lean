/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GeneralCompleteIntersectionResidue
public import MixedFujita.PulledCanonicalResidueTransitions

/-! 一般SNC座標と元Cartier因子和に正規化された実留数。 check-290：任意の選択SNC座標を先頭へ移す実有限置換を内部構成し、元の一般IsSNCChartから実閉層の商環・微分基底・純正規化留数・元周囲frame単元を構成。先頭座標という追加仮定を除去した。全法線方程式の同時変更で留数が単元比の積により変換する厳密公式を証明。元SNC成分の実イデアルと実Cartier方程式から各単元比を内部取得し、元K_X+ΣE_iの積局所方程式と、その同じ元方程式に正規化された実SNC閉層留数を供給。切断側の基底・留数・置換・単元比や中間商環の整性は追加仮定ではない。最終成分の標準層との同型・大域SNC随伴・数値随伴は残る。 -/

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


/-- The original canonical Cartier equation times ALL actual cut equations
is exactly the ORIGINAL K_X+SUM E_i equation. -/
theorem canonicalPlusCartierSum_local_equation
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n m : ℕ}
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c : EtaleChart K X n) (E : Fin m → CartierDivisor X)
    (g : Fin m → Γ(X, c.U)) (hg : ∀ i, g i ≠ 0)
    (hEq : ∀ i, rationalUnitClass X c.U
      (Additive.ofMul (regularEquationRationalUnit X c.U (g i) (hg i))) = E i |_ c.U) :
    rationalUnitClass X c.U (Additive.ofMul
      (etaleChartCanonicalEquation c₀ c * ∏ i, regularEquationRationalUnit X c.U (g i) (hg i))) =
        (canonicalDivisor n c₀ hcover + ∑ i, E i) |_ c.U := by
  classical
  have hs (s : Finset (Fin m)) : rationalUnitClass X c.U
      (Additive.ofMul (∏ i ∈ s, regularEquationRationalUnit X c.U (g i) (hg i))) =
        (∑ i ∈ s, E i) |_ c.U := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, ofMul_one, map_zero, Finset.sum_empty]
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_zero]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, ofMul_mul, map_add, hEq i, ih, Finset.sum_insert hi]
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add]
  rw [ofMul_mul, map_add, ← canonicalDivisor_restrict c₀ hcover c, hs Finset.univ]
  simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_add]


/-- Actual SNC component ideals and actual Cartier equations internally
supply EACH exact unit ratio, without an equation-change certificate. -/
theorem snc_original_cartier_equations_units
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n m : ℕ} (c : EtaleChart K X n) (ξ : Fin m → X) (τ : Fin m → Fin n)
    (hc : IsSNCChart c ξ (fun i => some (τ i)))
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X))
    (g : Fin m → Γ(X, c.U)) (hg : ∀ i, g i ≠ 0)
    (hEq : ∀ i, rationalUnitClass X c.U
      (Additive.ofMul (regularEquationRationalUnit X c.U (g i) (hg i))) = E i |_ c.U) :
    ∃ u : Fin m → Γ(X, c.U)ˣ, ∀ i, g i = ↑(u i) * c.coords (MvPolynomial.X (τ i)) := by
  classical
  have hu (i : Fin m) : ∃ u : Γ(X, c.U)ˣ, g i = ↑u * c.coords (MvPolynomial.X (τ i)) := by
    have he : Ideal.span {c.coords (MvPolynomial.X (τ i))} = Ideal.span {g i} := by
      rw [← effectiveCartierIdealSheaf_ideal_eq_span (E i) (hE i) ⟨c.U, c.isAffine⟩ (g i) (hg i) (hEq i), hI i]
      simpa only [Option.elim_some] using (vanishingIdeal_closure_ideal_sncChart c ξ _ hc i).symm
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
    exact ⟨u, by simpa only [mul_comm] using hu.symm⟩
  choose u hu using hu
  exact ⟨u, hu⟩


/-- Actual SNC chart equations give the full actual affine stratum quotient
kernel and surjectivity internally. No ideal-kernel certificate is supplied. -/
theorem snc_affine_selected_stratum_quotient_data
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n m : ℕ} (c : EtaleChart K X n) (ξ : Fin m → X) (τ : Fin m → Fin n)
    (hc : IsSNCChart c ξ (fun i => some (τ i))) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let q := (I.subschemeι.app c.U).hom
    Function.Surjective q ∧ RingHom.ker q =
      Ideal.span (Set.range fun i : Fin m => c.coords (MvPolynomial.X (τ i))) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  have hI : I.ideal ⟨c.U, c.isAffine⟩ =
      Ideal.span (Set.range fun i : Fin m => c.coords (MvPolynomial.X (τ i))) := by
    dsimp only [I]
    rw [snc_all_stratumIdeal_eq_iSup, Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    change (⨆ i : Fin m, (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X)).ideal ⟨c.U, c.isAffine⟩) = _
    simp_rw [vanishingIdeal_closure_ideal_sncChart c ξ _ hc, Option.elim_some]
    exact (Ideal.span_range_eq_iSup _).symm
  dsimp only
  refine ⟨I.subschemeι_app_surjective ⟨c.U, c.isAffine⟩, ?_⟩
  exact (I.ker_subschemeι_app ⟨c.U, c.isAffine⟩).trans hI


/-- GENERAL original SNC coordinates internally construct an adapted basis,
a true selected-coordinate residue and the exact original ambient frame unit.
No prefix-normal-form, permutation, cut basis, conormal or residue is supplied. -/
theorem snc_affine_selected_stratum_pulled_residue
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c : EtaleChart K X (m + r)) (ξ : Fin m → X) (τ : Fin m → Fin (m + r))
    (hc : IsSNCChart c ξ (fun i => some (τ i))) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let A := Γ(X, c.U)
    let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
    let q : A →+* B := (I.subschemeι.app c.U).hom
    let : Algebra A B := q.toAlgebra
    let : Algebra K B := (q.comp (algebraMap K A)).toAlgebra
    let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
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
  let : Algebra K B := (q.comp (algebraMap K A)).toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
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


/-- ORIGINAL Cartier component equations on a GENERAL SNC chart construct
both the ORIGINAL K_X+SUM E_i local equation and the normalized actual stratum
residue for those very equations. Every equation unit ratio, adapted basis,
residue and original ambient frame unit is constructed internally. -/
theorem snc_original_cartier_sum_pulled_residue
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (c₀ : EtaleChart K X (m + r))
    (hcover : iSup (fun c : EtaleChart K X (m + r) => c.U) = ⊤)
    (c : EtaleChart K X (m + r)) (ξ : Fin m → X) (τ : Fin m → Fin (m + r))
    (hc : IsSNCChart c ξ (fun i => some (τ i)))
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (hI : ∀ i, effectiveCartierIdealSheaf (E i) (hE i) = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X))
    (g : Fin m → Γ(X, c.U)) (hg : ∀ i, g i ≠ 0)
    (hEq : ∀ i, rationalUnitClass X c.U
      (Additive.ofMul (regularEquationRationalUnit X c.U (g i) (hg i))) = E i |_ c.U) :
    let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
    let A := Γ(X, c.U)
    let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
    let q : A →+* B := (I.subschemeι.app c.U).hom
    let : Algebra A B := q.toAlgebra
    let : Algebra K B := (q.comp (algebraMap K A)).toAlgebra
    let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    rationalUnitClass X c.U (Additive.ofMul (etaleChartCanonicalEquation c₀ c *
      ∏ i, regularEquationRationalUnit X c.U (g i) (hg i))) =
        (canonicalDivisor (m + r) c₀ hcover + ∑ i, E i) |_ c.U ∧
    ∃ (e : Fin (m + r) ≃ Fin (m + r)) (b : Module.Basis (Fin r) B Ω[B⁄K])
      (R : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K]) (a : Bˣ),
      (∀ i, e (Fin.castAdd r i) = τ i) ∧
      (∀ i, b i = D K B (q (c.coords (MvPolynomial.X (e (Fin.natAdd m i)))))) ∧
      (∀ z : Fin r → Ω[A⁄K],
        R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
          (Fin.append (fun i => D K A (g i)) z)) =
            exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) ∧
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r) (etaleCoordinateBasis c.coords c.formallyEtale)) =
        (a : B) • exteriorPower.ιMulti B r b := by
  classical
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let A := Γ(X, c.U)
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ c.U)
  let q : A →+* B := (I.subschemeι.app c.U).hom
  let : Algebra A B := q.toAlgebra
  let : Algebra K B := (q.comp (algebraMap K A)).toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  dsimp only
  refine ⟨canonicalPlusCartierSum_local_equation c₀ hcover c E g hg hEq, ?_⟩
  obtain ⟨e, b, R, a, he, hb, hR, _ha, hframe⟩ := snc_affine_selected_stratum_pulled_residue c ξ τ hc
  obtain ⟨u, hu⟩ := snc_original_cartier_equations_units c ξ τ hc E hE hI g hg hEq
  obtain ⟨_hsurj, hker⟩ := snc_affine_selected_stratum_quotient_data c ξ τ hc
  have hzero (i : Fin m) : algebraMap A B (c.coords (MvPolynomial.X (τ i))) = 0 :=
    RingHom.mem_ker.mp (hker ▸ Ideal.subset_span (Set.mem_range_self i))
  let v : Bˣ := Units.map q.toMonoidHom (∏ i, u i)
  let R' : (B ⊗[A] (⋀[A]^(m + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K] :=
    R.trans (LinearEquiv.smulOfUnit (M := ⋀[B]^r Ω[B⁄K]) v⁻¹)
  have hv : (v : B) = algebraMap A B (∏ i, (u i : A)) := by
    simp only [v, Units.coe_map, Units.coe_prod]
    rfl
  refine ⟨e, b, R', v⁻¹ * a, he, hb, ?_, ?_⟩
  · intro z
    change (↑v⁻¹ : B) • R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
      (Fin.append (fun i => D K A (g i)) z)) = _
    have hnormal : (fun i => D K A (g i)) =
        (fun i => D K A ((u i : A) * c.coords (MvPolynomial.X (τ i)))) :=
      funext fun i => congrArg (D K A) (hu i)
    have hscaled : R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
        (Fin.append (fun i => D K A (g i)) z)) =
          (v : B) • exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z) := by
      rw [hnormal, ← pulled_complete_intersection_equation_wedge_scaling m r
        (fun i => c.coords (MvPolynomial.X (τ i))) (fun i => (u i : A)) hzero
          (etaleCoordinateBasis c.coords c.formallyEtale) z, map_smul, hR]
      exact congrArg (fun t : B => t • exteriorPower.ιMulti B r
        (KaehlerDifferential.map K K A B ∘ z)) hv.symm
    have hcancel (w : ⋀[B]^r Ω[B⁄K]) : (↑v⁻¹ : B) • ((v : B) • w) = w := by
      rw [smul_smul]
      exact (congrArg (fun t : B => t • w) v.inv_val).trans (one_smul B w)
    exact (congrArg (fun w : ⋀[B]^r Ω[B⁄K] => (↑v⁻¹ : B) • w) hscaled).trans (hcancel _)

  · change (↑v⁻¹ : B) • R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (m + r)
      (etaleCoordinateBasis c.coords c.formallyEtale)) = _
    exact (congrArg (fun w : ⋀[B]^r Ω[B⁄K] => (↑v⁻¹ : B) • w) hframe).trans (smul_smul _ _ _)

end MixedFujita
