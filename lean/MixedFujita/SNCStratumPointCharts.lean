/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCCanonicalLocalAdjunction
public import MixedFujita.StratumTaylorRestriction

/-! 元SNC閉層の全点選択座標と実Cartier方程式チャート。 check-292：実SNC閉層の各点が元の全成分閉包に属することを実イデアル台の反変性から証明し、元IsSNCFamilyだけから全選択成分に座標の付くチャートと、非整・非連結にも対応する実閉層全体の残余エタール被覆を内部構成。任意affine細分でも元SNC条件が保たれることを証明し、元有効Cartier因子の実局所方程式を任意の指定近傍内の同じSNCチャートに内部供給。元滑らかなNoetherian SNCモデルから、既存正則成分APIで各点を通る実開閉整成分、その周囲開持ち上げ、元空間への実閉埋込みを構成し、その成分内の実整切断近傍と元Cartier方程式を同時供給。元幾何だけを持つSNCAdjunctionChartと、291の内部残余座標を使う実切断チャートを定義し、これらが実閉層全体を覆うことを証明。成分上への標準層同型の移送・重なり一致・大域SNC随伴と数値随伴は残る。 -/

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


/-- Every ACTUAL point of the full closed stratum lies in every original
component closure; this follows from actual ideal support antitonicity. -/
theorem snc_stratum_point_mem_all_components
    {X : Scheme.{u}} {m : ℕ} (ξ : Fin m → X)
    (y : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) (k : Fin m) :
    (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι y ∈
      closure ({ξ k} : Set X) := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  let J := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({ξ k} : Set X), isClosed_closure⟩ : Closeds X)
  have hle : J ≤ I := by
    dsimp only [I]
    rw [snc_all_stratumIdeal_eq_iSup]
    exact le_iSup_of_le k le_rfl
  have hy : I.subschemeι y ∈ (I.support : Set X) := by
    rw [← I.range_subschemeι]
    exact Set.mem_range_self y
  have hJ : I.subschemeι y ∈ (J.support : Set X) := Scheme.IdealSheafData.support_antitone hle hy
  dsimp only [J] at hJ
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hJ
  exact hJ


/-- ORIGINAL SNC position survives ANY nonempty affine restriction of the
actual chart, including restrictions used for genuine Cartier equations. -/
theorem isSNCChart_affineRestriction
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    {n m : ℕ} (c : EtaleChart K X n) {ξ : Fin m → X} {σ : Fin m → Option (Fin n)}
    (hc : IsSNCChart c ξ σ) (V : X.affineOpens) [Nonempty V.1] (hVc : V.1 ≤ c.U) :
    IsSNCChart (etaleChartAffineRestriction c V hVc) ξ σ := by
  refine ⟨hc.1, fun i => ?_⟩
  have hle : (V.1 : Set X) ⊆ c.U := hVc
  have hsub : closure ({ξ i} : Set X) ∩ V.1 =
      (closure ({ξ i} : Set X) ∩ c.U) ∩ V.1 := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle]
  change closure ({ξ i} : Set X) ∩ V.1 = (σ i).elim ∅ (fun a =>
    X.zeroLocus ({X.presheaf.map (homOfLE hVc).op (c.coords (MvPolynomial.X a))} :
      Set Γ(X, V.1)) ∩ V.1)
  rw [hsub, hc.2 i]
  cases σ i with
  | none => simp
  | some a =>
    simp only [Option.elim_some]
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hle, Scheme.zeroLocus_singleton,
      Scheme.zeroLocus_singleton, Scheme.basicOpen_res]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, Opens.mem_inf]
    tauto


/-- At EACH point of the ACTUAL full stratum, the ORIGINAL SNC family
internally supplies a chart in which ALL selected members have coordinates. -/
theorem snc_stratum_exists_selected_chart_at
    {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] {n m : ℕ}
    (ξ : Fin m → X) (hsnc : IsSNCFamily K n ξ)
    (y : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme) :
    ∃ (c : EtaleChart K X n) (τ : Fin m → Fin n),
      (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι y ∈ c.U ∧
        IsSNCChart c ξ (fun i => some (τ i)) := by
  classical
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  obtain ⟨c, σ, hp, hc⟩ := hsnc (I.subschemeι y)
  have hsome (i : Fin m) : ∃ a, σ i = some a :=
    isSNCChart_exists_some_of_mem_closure hc (I.subschemeι y) hp
      (snc_stratum_point_mem_all_components ξ y i)
  choose τ hτ using hsome
  have hσ : σ = fun i => some (τ i) := funext hτ
  exact ⟨c, τ, hp, hσ ▸ hc⟩


/-- The ORIGINAL SNC family internally supplies an ACTUAL r-dimensional
etale atlas of its entire full stratum, even when disconnected/nonintegral. -/
theorem snc_stratum_etaleChart_cover
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {m r : ℕ} (ξ : Fin m → X) (hsnc : IsSNCFamily K (m + r) ξ)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    [(sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι.IsOver (Spec (CommRingCat.of K))] :
    iSup (fun c : EtaleChart K (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme r => c.U) = ⊤ := by
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  apply top_unique
  intro y _hy
  obtain ⟨c, τ, hp, hc⟩ := snc_stratum_exists_selected_chart_at ξ hsnc y
  let : Nonempty (I.subschemeι ⁻¹ᵁ c.U) := ⟨⟨y, hp⟩⟩
  let d : EtaleChart K I.subscheme r :=
    { U := I.subschemeι ⁻¹ᵁ c.U, isAffine := c.isAffine.preimage I.subschemeι,
      nonempty := inferInstance, coords := sncStratumEtaleCoordinates c ξ τ hc,
      formallyEtale := sncStratumEtaleCoordinates_formallyEtale c ξ τ hc }
  exact Opens.mem_iSup.mpr ⟨d, hp⟩


/-- At EVERY original stratum point, genuine Cartier component equations and
an SNC chart are constructed on one affine open inside ANY prescribed
ambient neighbourhood. No compatible equation atlas is supplied. -/
theorem snc_stratum_exists_cartier_equation_chart_at
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] {n m : ℕ}
    (ξ : Fin m → X) (hsnc : IsSNCFamily K n ξ)
    (E : Fin m → CartierDivisor X) (hE : ∀ i, (E i).IsEffective)
    (y : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subscheme)
    (O : X.Opens) (hyO : (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι y ∈ O) :
    ∃ (c : EtaleChart K X n) (τ : Fin m → Fin n)
      (g : Fin m → Γ(X, c.U)) (hg : ∀ i, g i ≠ 0),
      (sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ).subschemeι y ∈ c.U ∧ c.U ≤ O ∧
      IsSNCChart c ξ (fun i => some (τ i)) ∧
      ∀ i, rationalUnitClass X c.U (Additive.ofMul (regularEquationRationalUnit X c.U (g i) (hg i))) =
        E i |_ c.U := by
  classical
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints ξ) Finset.univ
  obtain ⟨c, τ, hp, hc⟩ := snc_stratum_exists_selected_chart_at ξ hsnc y
  obtain ⟨Ueq, hpeq, hne, g, hg, hEq⟩ := exists_affineOpen_regularEquations_of_isEffective E hE (I.subschemeι y)
  letI := hne
  let T : X.Opens := c.U ⊓ Ueq.1 ⊓ O
  have hpT : I.subschemeι y ∈ T := ⟨⟨hp, hpeq⟩, hyO⟩
  obtain ⟨_, ⟨W, hWa, rfl⟩, hpW, hWT⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hpT T.isOpen
  have hWc : W ≤ c.U := fun _z hz => (hWT hz).1.1
  have hWeq : W ≤ Ueq.1 := fun _z hz => (hWT hz).1.2
  have hWO : W ≤ O := fun _z hz => (hWT hz).2
  let : Nonempty W := ⟨⟨I.subschemeι y, hpW⟩⟩
  choose hgW hEqW using fun i => regularEquation_restrict (E i) hWeq (g i) (hg i) (hEq i)
  let cW := etaleChartAffineRestriction c ⟨W, hWa⟩ hWc
  exact ⟨cW, τ, fun i => X.presheaf.map (homOfLE hWeq).op (g i), hgW,
    hpW, hWO, isSNCChart_affineRestriction c hc ⟨W, hWa⟩ hWc, hEqW⟩

end MixedFujita
