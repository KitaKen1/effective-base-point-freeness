/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveAmpleMixedIntersectionPositive
public import MixedFujita.NefCoherentMixedEuler
public import MixedFujita.NefCurveMixedEulerNonnegative
public import MixedFujita.EffectiveCartierCutPureDimension
public import MixedFujita.ReducedCenterFactorization
public import MixedFujita.ProperBaseMixedEulerNilpotence
public import MixedFujita.RestrictedConcentrationPreservation
public import MixedFujita.ProperCurveOrderBounds
public import MixedFujita.ActualCartierPullbackNonvanishing
public import MixedFujita.CartierSectionZeroIdeal
public import MixedFujita.NefNumericalZeroMixedPowers
public import MixedFujita.CartierNumericalTriviality
public import MixedFujita.CartierPullbackDegreeComparison
public import MixedFujita.ProperSurjectiveComponentImage
public import OAI.AlgebraicGeometry.NumericalDimension.ExceptionalFibers

/-!
A nef Cartier divisor of numerical dimension zero is numerically trivial (Kleiman's criterion in
the form needed for the base point free theorem). Let X be an integral proper scheme of dimension
n ≥ 1 over an algebraically closed field of characteristic zero, J ample and D nef with
D · J^(n−1) = 0. Then every proper smooth curve mapping to X has degree zero against D.

The proof cuts down along the image of the curve and uses no Hodge index theorem:

* a section σ of m J vanishing on the image of the curve exists for some m ≥ 1, because h⁰(m J)
  grows like m^(dim X) while the sections pulled back to the curve grow at most linearly;
* the cut of X by σ has D · J^(n−2)-degree m · D · J^(n−1) = 0, all mixed Euler coefficients of
  integral closed subschemes of the cut are nonnegative, so the irreducible component of the cut
  that contains the image (of dimension n − 1 by the principal ideal theorem) also has degree zero;
* by induction the curve ends in a curve, where the degree is a positive multiple of D · [curve].
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower

/-- A curve whose image is one point has zero pullback degree. -/
theorem constant_curve_pullbackDegree_eq_zero
    (K : Type u) [Field K] {V C : Scheme.{u}} [IsIntegral V] [IsIntegral C]
    [V.Over (Spec (CommRingCat.of K))] [IsProper (V ↘ Spec (CommRingCat.of K))]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1)
    (ψ : C ⟶ V) [ψ.IsOver (Spec (CommRingCat.of K))] (hconst : ∀ a b : C, ψ a = ψ b)
    (D : CartierDivisor V) :
    cartierCurvePullbackDegree (K := K) D ψ = 0 := by
  have : IsProper (ψ ≫ (V ↘ Spec (CommRingCat.of K))) := by
    rw [comp_over ψ (Spec (CommRingCat.of K))]
    infer_instance
  have : IsProper ψ := IsProper.of_comp ψ (V ↘ Spec (CommRingCat.of K))
  obtain ⟨c₀⟩ : Nonempty C := inferInstance
  set y := ψ c₀ with hy
  have hrange : Set.range ψ = {y} := by
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      exact hconst c c₀
    · rintro rfl
      exact ⟨c₀, rfl⟩
  have hclosed : IsClosed ({y} : Set V) := hrange ▸ ψ.isClosedMap.isClosed_range
  have hsub : Set.range ψ ⊆ ((⟨closure {y}, isClosed_closure⟩ : Closeds V) : Set V) := by
    rw [hrange]
    exact subset_closure
  obtain ⟨ψ₀, hψ₀⟩ := reduced_source_exists_closed_center_factor ψ _ hsub
  change C ⟶ pointClosureScheme y at ψ₀
  change ψ₀ ≫ pointClosureι y = ψ at hψ₀
  have : IsProper (pointClosureScheme y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (pointClosureι y ≫ (V ↘ Spec (CommRingCat.of K)))
    infer_instance
  have hdimP : topologicalKrullDim (pointClosureScheme y) ≤ (0 : ℕ) := by
    rw [pointClosureScheme_topologicalKrullDim, hclosed.closure_eq]
    have : Subsingleton ({y} : Set V) := Set.subsingleton_singleton.coe_sort
    exact_mod_cast topologicalKrullDim_zero_of_discreteTopology ({y} : Set V)
  obtain ⟨DP, ⟨aD⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D (pointClosureι y)
  rw [← hψ₀, cartierCurvePullbackDegree_comp_of_representation hC _ ψ₀ D DP aD,
    ← properSmoothCurve_pulled_singleton_eq_curvePullbackDegree K hC ψ₀ DP 0]
  let : (CohomologyAux.unitModule C).IsCoherent := invertible_module_isCoherent _
  exact proper_cartierPulledModuleMixedEulerDifference_vanish_of_base_dimension K 0 hdimP ψ₀
    (CohomologyAux.unitModule C) [DP] (by simp) 0

/-- The pullback of sections along a curve as a linear map over the base field. -/
noncomputable def curveSectionPullbackLinear
    (K : Type u) [Field K] {V C : Scheme.{u}} [IsIntegral V] [IsIntegral C]
    [V.Over (Spec (CommRingCat.of K))] [C.Over (Spec (CommRingCat.of K))]
    (ψ : C ⟶ V) [ψ.IsOver (Spec (CommRingCat.of K))] (P : CartierDivisor V)
    (E : CartierDivisor C) (e : (Scheme.Modules.pullback ψ).obj P.sheaf ≅ E.sheaf) :
    Γ(P.sheaf, ⊤) →ₗ[K] Γ(E.sheaf, ⊤) where
  toFun := cartierPullbackGlobalSectionViaIso P ψ E e
  map_add' := map_add _
  map_smul' := cartierPullbackGlobalSectionViaIso_smul_base ψ P E e

/-- A nonzero section of a multiple of an ample divisor vanishes along the image of a proper
smooth curve, once the dimension is at least two: h⁰(m J) ≥ c m^d infinitely often, while the
pulled back sections live in a space of dimension at most m · b + 1. -/
theorem exists_nsmul_section_vanishing_on_curve
    (K : Type u) [Field K] [IsAlgClosed K] {V C : Scheme.{u}} [IsIntegral V] [IsIntegral C]
    [V.Over (Spec (CommRingCat.of K))] [IsProper (V ↘ Spec (CommRingCat.of K))]
    [C.Over (Spec (CommRingCat.of K))] [IsProper (C ↘ Spec (CommRingCat.of K))]
    [Smooth (C ↘ Spec (CommRingCat.of K))] (hC : topologicalKrullDim C = 1)
    (d : ℕ) (hdV : topologicalKrullDim V = d) (hd : 2 ≤ d)
    (J : CartierDivisor V) (hJ : CartierIsAmpleProj K J)
    (ψ : C ⟶ V) [ψ.IsOver (Spec (CommRingCat.of K))] :
    ∃ (m : ℕ) (σ : Γ((m • J).sheaf, ⊤)) (_ : σ ≠ 0),
      Set.range ψ ⊆ cartierSectionZeroLocus (m • J) σ := by
  obtain ⟨JC, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor J ψ
  obtain ⟨d', hd', c, hc, hfreq⟩ := cartierIsAmpleProj_isBig hdV (by omega) hJ
  have hdd : d' = d := by
    have h := hd'.symm.trans hdV
    exact_mod_cast h
  subst hdd
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace (C ↘ Spec (CommRingCat.of K))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := C)).exists_closed_singleton Set.univ_nonempty
  set b := properCurveOrderBound (K := K) hC JC with hb
  have hev : ∀ᶠ m : ℕ in atTop, ((m * b + 1 : ℕ) : ℝ) < c * (m : ℝ) ^ d' := by
    filter_upwards [eventually_ge_atTop (⌈((b : ℝ) + 1) / c⌉₊ + 1)] with m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hm
    have hcm : (b : ℝ) + 1 < c * m := by
      have h1 : ((b : ℝ) + 1) / c < m := by
        have := Nat.le_ceil (((b : ℝ) + 1) / c)
        have h2 : ((⌈((b : ℝ) + 1) / c⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
        push_cast at h2
        linarith
      rw [div_lt_iff₀ hc] at h1
      linarith
    have hpow : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ d' := pow_le_pow_right₀ hm1 hd
    have hsq : c * (m : ℝ) ^ 2 = (c * m) * m := by ring
    push_cast
    calc (m : ℝ) * b + 1 ≤ (m : ℝ) * (b + 1) := by nlinarith
      _ < (c * m) * m := by nlinarith
      _ = c * (m : ℝ) ^ 2 := hsq.symm
      _ ≤ c * (m : ℝ) ^ d' := mul_le_mul_of_nonneg_left hpow hc.le
  obtain ⟨m, hm1, hm2⟩ := (hfreq.and_eventually hev).exists
  have hlt : (m * b + 1 : ℕ) < Module.finrank K Γ((m • J).sheaf, ⊤) := by
    exact_mod_cast hm2.trans_le hm1
  have hupper : Module.finrank K Γ((m • JC).sheaf, ⊤) ≤ m * b + 1 :=
    properSmoothCurve_gradedSection_finrank_le_linearBound (K := K) hC JC m x hx
  let : FiniteDimensional K Γ((m • J).sheaf, ⊤) :=
    Module.finite_of_finrank_pos (by omega)
  let : FiniteDimensional K Γ((m • JC).sheaf, ⊤) :=
    geometricSmoothCartier_closedPoint_finiteDimensional_of_order_bound (K := K) 1 hC (m • JC) x hx
      (m * b) (properSmoothCurve_closedPoint_gradedVanishingOrder_le_linearBound
        (K := K) hC JC m x hx)
  let e := cartierPullbackGradedIso J ψ JC a m
  let L := curveSectionPullbackLinear K ψ (m • J) (m • JC) e
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by omega)
  obtain ⟨σ, hσker, hσ⟩ := (Submodule.ne_bot_iff _).mp hker
  refine ⟨m, σ, hσ, ?_⟩
  rintro _ ⟨y, rfl⟩ hy
  have hzero : cartierPullbackGlobalSectionViaIso (m • J) ψ (m • JC) e σ = 0 := hσker
  have hmem : y ∈ cartierSectionNonvanishingOpen (m • JC)
      (cartierPullbackGlobalSectionViaIso (m • J) ψ (m • JC) e σ) := by
    rw [cartierActualPullback_nonvanishingOpen]
    exact hy
  have hne : Nonempty (cartierSectionNonvanishingOpen (m • JC)
      (cartierPullbackGlobalSectionViaIso (m • J) ψ (m • JC) e σ)) := ⟨⟨y, hmem⟩⟩
  exact (cartierSectionNonvanishingOpen_nonempty_iff _ _).mp hne hzero

theorem list_forallTwo_replicate_of_rel {α β : Type*} (R : α → β → Prop) {a : α} {b : β}
    (h : R a b) : ∀ n : ℕ, List.Forall₂ R (List.replicate n a) (List.replicate n b)
  | 0 => List.Forall₂.nil
  | n + 1 => List.Forall₂.cons h (list_forallTwo_replicate_of_rel R h n)

/-- Kleiman's criterion along a curve. On an integral proper scheme V of dimension r + 1 with J
ample, a nef D with D · J^r = 0 has degree zero on every proper smooth curve over K mapping to V.
A section of m J vanishing on the image of the curve cuts V; the component of the cut through
the image has dimension r and again zero mixed degree, by nonnegativity on the cut. -/
theorem nef_mixed_zero_curve_pullbackDegree_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (r : ℕ) :
    ∀ (V : Scheme.{u}) [IsIntegral V] [V.Over (Spec (CommRingCat.of K))]
      [IsProper (V ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim V = (r + 1 : ℕ) →
      ∀ J : CartierDivisor V, CartierIsAmpleProj K J →
      ∀ D : CartierDivisor V, CartierIsNef K D →
      cartierMixedEulerDifference K (D :: List.replicate r J) 0 = 0 →
      ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
        [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
        topologicalKrullDim C = 1 → ∀ (ψ : C ⟶ V) [ψ.IsOver (Spec (CommRingCat.of K))],
        cartierCurvePullbackDegree (K := K) D ψ = 0 := by
  induction r with
  | zero =>
    intro V _ _ _ hdimV J hJ D hD hzero C _ _ _ _ hC ψ _
    by_cases hconst : ∀ a b : C, ψ a = ψ b
    · exact constant_curve_pullbackDegree_eq_zero K hC ψ hconst D
    · obtain ⟨a₁, b₁, hab⟩ : ∃ a b : C, ψ a ≠ ψ b := by
        by_contra hnot
        exact hconst fun a b => by
          by_contra hne
          exact hnot ⟨a, b, hne⟩
      have : IsProper (ψ ≫ (V ↘ Spec (CommRingCat.of K))) := by
        rw [comp_over ψ (Spec (CommRingCat.of K))]
        infer_instance
      have : IsProper ψ := IsProper.of_comp ψ (V ↘ Spec (CommRingCat.of K))
      let : SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of K)) :=
        geometricSmoothScheme_relativeDimension (K := K) 1 hC
      let := properOverField_scheme_isNoetherian (K := K) (X := C)
      have hcoh : ∀ y : V, Order.coheight y ≤ 1 := fun y => by
        exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hdimV.le
      obtain ⟨hfin, hdom⟩ := OAI.NumericalDimensionOne.finite_dominant_of_nonconstant_smooth_curve
        (C ↘ Spec (CommRingCat.of K)) ψ hcoh ⟨a₁, b₁, hab⟩
      obtain ⟨k, -, hformula⟩ := finite_dominant_exists_positive_top_mixed_multiplier K 1 le_rfl
        hdimV hC ⟨J, hJ⟩ ψ
      have h := hformula V (𝟙 V) [D] rfl 0
      rw [Category.comp_id] at h
      rw [← properSmoothCurve_pulled_singleton_eq_curvePullbackDegree K hC ψ D 0, h]
      have h0 : cartierPulledModuleMixedEulerDifference K (𝟙 V) (CohomologyAux.unitModule V)
          [D] 0 = 0 := by
        rw [show CohomologyAux.unitModule V = SheafOfModules.unit V.ringCatSheaf from rfl,
          cartierPulledModuleMixedEulerDifference_id_unit]
        simpa using hzero
      rw [h0, mul_zero]
  | succ r ih =>
    intro V _ _ _ hdimV J hJ D hD hzero C _ _ _ _ hC ψ _
    obtain ⟨m, σ, hσ, hrange⟩ :=
      exists_nsmul_section_vanishing_on_curve K hC (r + 1 + 1) hdimV (by omega) J hJ ψ
    let G := cartierSectionZeroDivisor (m • J) σ hσ
    have hG : G.IsEffective := cartierSectionZeroDivisor_isEffective _ _ _
    let I := effectiveCartierIdealSheaf G hG
    let Y := I.subscheme
    let p : Y ⟶ V := I.subschemeι
    let : Y.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (V ↘ Spec (CommRingCat.of K))⟩
    let : p.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
      change IsProper (p ≫ (V ↘ Spec (CommRingCat.of K)))
      infer_instance
    have hdimY : topologicalKrullDim Y ≤ (r + 1 : ℕ) :=
      effectiveCartierCut_topologicalKrullDim_le G hG (r + 1) hdimV.le
    let dirs := D :: List.replicate r J
    have hlen : dirs.length = r + 1 := by simp [dirs]
    have hnefdirs : ∀ F ∈ dirs, CartierIsNef K F := by
      intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hD
      · rw [List.eq_of_mem_replicate hF]
        exact cartierIsAmpleProj_isNef hJ
    -- the cut by σ has zero mixed degree
    have hcut : cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y)
        dirs 0 = 0 := by
      have h1 := proper_cartierMixedEulerDifference_top_eq_effective_cut K dirs G 0 hG
        (by rw [hlen]; exact hdimV.le)
      change cartierPulledModuleMixedEulerDifference K p
        (SheafOfModules.unit Y.ringCatSheaf) dirs 0 = 0
      rw [← h1]
      change cartierMixedEulerDifference K
        ((m • J + principalCartierDivisor V (cartierSectionUnit (m • J) σ hσ)) :: dirs) 0 = 0
      rw [cartierMixedEulerDifference_direction_principal]
      have h2 := proper_cartierMixedEulerDifference_top_nsmul_factor K (r + 1 + 1) hdimV.le []
        dirs (by simp [hlen]) J 0 m
      simp only [List.nil_append] at h2
      rw [h2]
      have h3 : cartierMixedEulerDifference K (J :: dirs) 0 =
          cartierMixedEulerDifference K (D :: List.replicate (r + 1) J) 0 := by
        apply cartierMixedEulerDifference_perm
        rw [List.replicate_succ]
        exact List.Perm.swap _ _ _
      rw [h3, hzero, mul_zero]
    -- the curve factors through the cut
    have hrange' : Set.range ψ ⊆ (I.support : Set V) := by
      change Set.range ψ ⊆ ((cartierSectionZeroIdeal (m • J) σ hσ).support : Set V)
      rw [cartierSectionZeroIdeal_support (K := K)]
      exact hrange
    obtain ⟨ψ₁, hψ₁⟩ := reduced_source_exists_closed_center_factor ψ I.support hrange'
    have hle : I ≤ Scheme.IdealSheafData.vanishingIdeal I.support :=
      Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl
    let ψY : C ⟶ Y := ψ₁ ≫ Scheme.IdealSheafData.inclusion hle
    have hψY : ψY ≫ p = ψ := by
      simp only [ψY, p, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, hψ₁]
    -- the irreducible component of the cut through the curve
    have hirr : IsIrreducible (Set.range ψY) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ C).image ψY ψY.continuous.continuousOn
    obtain ⟨Z, hZ, hZsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
    obtain ⟨T₀, i₀, hT₀, hi₀, hrange₀, hdimT₀⟩ :=
      effectiveCartierCut_component_exists_integral_expected_dimension K (r + 1) hdimV G hG Z hZ
    obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1
      (isClosed_of_mem_irreducibleComponents Z hZ)
    let T := pointClosureScheme η
    let ιT : T ⟶ Y := pointClosureι η
    have hrangeT : Set.range ιT = Z := by
      rw [range_pointClosureι]
      exact hη
    have hdimT : topologicalKrullDim T = (r + 1 : ℕ) := by
      let := hi₀
      rw [closedImmersion_dimension_eq_of_range_eq ιT i₀ (hrangeT.trans hrange₀.symm), hdimT₀]
    have hsubT : Set.range ψY ⊆
        ((⟨closure {η}, isClosed_closure⟩ : Closeds Y) : Set Y) := by
      change Set.range ψY ⊆ closure {η}
      rw [hη.def]
      exact hZsub
    obtain ⟨ψT, hψT⟩ := reduced_source_exists_closed_center_factor ψY _ hsubT
    change C ⟶ T at ψT
    change ψT ≫ ιT = ψY at hψT
    let q : T ⟶ V := ιT ≫ p
    have : IsProper (T ↘ Spec (CommRingCat.of K)) := by
      change IsProper (ιT ≫ (Y ↘ Spec (CommRingCat.of K)))
      infer_instance
    have : q.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    have hψq : ψT ≫ q = ψ := by
      simp only [q, ← Category.assoc, hψT, hψY]
    have : ψT.IsOver (Spec (CommRingCat.of K)) := by
      constructor
      change ψT ≫ q ≫ (V ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K)
      rw [← Category.assoc, hψq, comp_over ψ (Spec (CommRingCat.of K))]
    -- nonnegativity on the cut forces zero degree on the component
    have hunit : ∀ (Z' : Scheme.{u}) [IsIntegral Z'] [Z'.Over (Spec (CommRingCat.of K))]
        [IsProper (Z' ↘ Spec (CommRingCat.of K))]
        (j : Z' ⟶ Y) [IsClosedImmersion j] [j.IsOver (Spec (CommRingCat.of K))],
        0 ≤ cartierPulledModuleMixedEulerDifference K (j ≫ p)
          (CohomologyAux.unitModule Z') dirs 0 := by
      intro Z' _ _ _ j _ _
      let : (CohomologyAux.unitModule Z').IsCoherent := invertible_module_isCoherent _
      exact proper_closed_pulled_nef_coherentMixedEuler_nonneg K r
        (j.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdimY) (j ≫ p) J hJ
        dirs hlen hnefdirs _ 0
    have hT0 : cartierPulledModuleMixedEulerDifference K q (CohomologyAux.unitModule T)
        dirs 0 = 0 := by
      by_contra hne
      have hpos : 0 < cartierPulledModuleMixedEulerDifference K (ιT ≫ p)
          (CohomologyAux.unitModule T) dirs 0 :=
        lt_of_le_of_ne (hunit T ιT) (Ne.symm hne)
      have h := proper_cartierPulledModuleMixedEulerDifference_top_unit_positive_of_closed_quotient
        K r hdimY p dirs (by omega) 0 hunit ιT hpos
      rw [hcut] at h
      exact lt_irrefl 0 h
    -- representatives on the component and the induction hypothesis
    obtain ⟨JT, ⟨aJ⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor J q
    obtain ⟨DT, ⟨aD⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D q
    obtain ⟨ET, ⟨aE⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor (0 : CartierDivisor V) q
    have hJT : CartierIsAmpleProj K JT := cartierIsAmpleProj_of_finite_pullback_over K q J JT hJ aJ
    have hDT : CartierIsNef K DT := cartierIsNef_of_pullback_representative K q D DT aD hD
    have hrep : List.Forall₂ (fun H F => Nonempty ((Scheme.Modules.pullback q).obj H.sheaf ≅ F.sheaf))
        dirs (DT :: List.replicate r JT) :=
      List.Forall₂.cons ⟨aD⟩ (list_forallTwo_replicate_of_rel _ ⟨aJ⟩ r)
    have hzeroT : cartierMixedEulerDifference K (DT :: List.replicate r JT) 0 = 0 := by
      have h := cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K q hrep 0 ET aE
      rw [proper_cartierMixedEulerDifference_top_base_independent K (r + 1) hdimT.le _
        (by simp) ET 0] at h
      rw [← h]
      exact hT0
    have hih := ih T hdimT JT hJT DT hDT hzeroT C hC ψT
    rw [← hψq, cartierCurvePullbackDegree_comp_of_representation hC q ψT D DT aD]
    exact hih

/-- **A nef divisor of numerical dimension zero is numerically trivial.** On an integral proper
scheme of dimension n ≥ 1 over an algebraically closed field of characteristic zero, a nef
Cartier divisor whose numerical dimension against an ample divisor is zero has degree zero on
every proper smooth curve over K mapping to the scheme. -/
theorem proper_nef_numericalDimension_zero_isNumericallyTrivial
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0) :
    CartierIsNumericallyTrivial K D := by
  intro C _ _ _ _ hC φ hφ
  have : φ.IsOver (Spec (CommRingCat.of K)) := ⟨hφ⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
  have h1 := (proper_nef_cartierNumericalDimension_zero_iff_positive_mixed_powers_vanish K
    (r + 1) hdim hn D J hD hJ).mp hzero ⟨1, by omega⟩ le_rfl
  have hmix : cartierMixedEulerDifference K (D :: List.replicate r J) 0 = 0 := by
    simpa [cartierMixedPowerIntersection, cartierMixedIntersection] using h1
  exact nef_mixed_zero_curve_pullbackDegree_eq_zero K r X hdim J hJ D hD hmix C hC φ

/-- Hence its negative is nef as well. -/
theorem proper_nef_numericalDimension_zero_neg_isNef
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D J : CartierDivisor X) (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n hdim D J = 0) :
    CartierIsNef K (-D) :=
  ((cartierIsNumericallyTrivial_iff_nef_and_neg_nef D).mp
    (proper_nef_numericalDimension_zero_isNumericallyTrivial K n hdim hn D J hD hJ hzero)).2

end MixedFujita
