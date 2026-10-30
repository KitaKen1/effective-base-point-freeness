/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BPFBaseLocusAmpleAdjoints
public import MixedFujita.RationalKltPerturbationThreshold
public import MixedFujita.MinimalLogCanonicalCenters
public import MixedFujita.RestrictedNumericalZeroLCCenter
public import MixedFujita.ArbitraryKltAnchorUniqueCenterIsolation
public import MixedFujita.NefNumericalZeroTriviality
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.ClosedPointRealizationFromLemmaThree

/-!
An isolated log canonical centre inside a stable base locus on which D is numerically trivial
(step 16, the base point free theorem).

Let (X, Δ) be a normal projective klt pair of dimension n ≥ 2, D nef with a D − (K_X + Δ) nef and
big, and m D a multiple with a nonzero section and a nonempty base locus B. Then there are a log
canonical pair (X, Δ₃), a point η with W = closure {η} ⊆ B, such that

* the non-klt locus of (X, Δ₃) is exactly W and W is a log canonical centre,
* every large adjoint j D − (K_X + Δ₃) is ample,
* D has degree zero on every proper smooth curve mapping into W.

The pair comes from Codex's base-source construction (`original_klt_bpf_exists_base_source_ample_adjoints_and_Serre_lifting`),
the exact rational threshold towards it, a minimal log canonical centre, the Noetherian
minimization to numerical dimension zero on the centre and the isolation of the centre; the
numerical triviality on W is `proper_nef_numericalDimension_zero_isNumericallyTrivial`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Lowering the coefficient of an effective perturbation keeps a pair klt over a point. -/
theorem logPairIsKltOverBasePoint_rational_perturbation_of_le
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D G : CartierDivisor X)
    (hG : G.IsEffective) (p q p' q' : ℕ) (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hle : (p : ℚ) / q ≤ (p' : ℚ) / q') (x : X)
    (h : LogPairIsKltOverBasePoint (𝟙 X) x c f (q' * d) (q' • D + (d * p') • G)) :
    LogPairIsKltOverBasePoint (𝟙 X) x c f (q * d) (q • D + (d * p) • G) := by
  intro T _ _ _ _ ρ _ _ _ hρ cT t ht hx
  have h' := h T ρ hρ cT t ht hx
  rw [logDiscrepancyDivisor_rational_perturbation ρ hρ c f d p' q' D G cT etaleCharts_cover,
    cartierCoefficient_sub, cartierCoefficient_nsmul, cartierCoefficient_nsmul] at h'
  rw [logDiscrepancyDivisor_rational_perturbation ρ hρ c f d p q D G cT etaleCharts_cover,
    cartierCoefficient_sub, cartierCoefficient_nsmul, cartierCoefficient_nsmul]
  have hg : 0 ≤ cartierCoefficient (cartierPullback ρ G) t :=
    cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ G hG) t
  have hcross : (p : ℤ) * q' ≤ (p' : ℤ) * q := by
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hq
    have hq'0 : (0 : ℚ) < q' := by exact_mod_cast hq'
    rw [div_le_div_iff₀ hq0 hq'0] at hle
    exact_mod_cast hle
  set ℓ := cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t
  set g := cartierCoefficient (cartierPullback ρ G) t
  push_cast at h' ⊢
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
  have hq'0 : (0 : ℤ) < q' := by exact_mod_cast hq'
  have hd0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  have hmul : (d : ℤ) * p * q' * g ≤ (d : ℤ) * p' * q * g := by
    have := mul_le_mul_of_nonneg_left hcross (mul_nonneg hd0 hg)
    nlinarith
  nlinarith

/-- A nef divisor has degree zero on every proper smooth curve mapping into the closure of a point
η, if its restriction to the closure has numerical dimension zero for every ample divisor and every
representative of the restriction. -/
theorem curve_into_pointClosure_pullbackDegree_eq_zero
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hproj : ∃ A : CartierDivisor X, CartierIsAmpleProj K A)
    (D : CartierDivisor X) (hD : CartierIsNef K D) (η : X)
    [IsProper (pointClosureScheme η ↘ Spec (CommRingCat.of K))]
    (hzero : ∀ (k : ℕ) (hdim : topologicalKrullDim (pointClosureScheme η) = k)
      (LZ HZ : CartierDivisor (pointClosureScheme η))
      (_aL : (Scheme.Modules.pullback (pointClosureι η)).obj D.sheaf ≅ LZ.sheaf),
      CartierIsAmpleProj K HZ → cartierNumericalDimension K k hdim LZ HZ = 0)
    (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
    [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))]
    (hC : topologicalKrullDim C = 1) (φ : C ⟶ X) [φ.IsOver (Spec (CommRingCat.of K))]
    (hφ : Set.range φ ⊆ closure {η}) :
    cartierCurvePullbackDegree (K := K) D φ = 0 := by
  obtain ⟨φW, hφW⟩ := reduced_source_exists_closed_center_factor φ
    ⟨closure {η}, isClosed_closure⟩ hφ
  change C ⟶ pointClosureScheme η at φW
  change φW ≫ pointClosureι η = φ at hφW
  have : φW.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change φW ≫ pointClosureι η ≫ (X ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K)
    rw [← Category.assoc, hφW, comp_over φ (Spec (CommRingCat.of K))]
  obtain ⟨LZ, ⟨aL⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D (pointClosureι η)
  rw [← hφW, cartierCurvePullbackDegree_comp_of_representation hC _ φW D LZ aL]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, topologicalKrullDim (pointClosureScheme η) = k :=
    ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · apply constant_curve_pullbackDegree_eq_zero K hC φW _ LZ
    intro a b
    have : Subsingleton (pointClosureScheme η) := subsingleton_of_topologicalKrullDim_eq_zero
      (by simpa using hk)
    exact Subsingleton.elim _ _
  · obtain ⟨HZ, hHZ⟩ := integral_closed_source_exists_original_ample_cartier K (pointClosureι η)
      hproj
    have hLZ : CartierIsNef K LZ :=
      cartierIsNef_of_pullback_representative K (pointClosureι η) D LZ aL hD
    have htriv := proper_nef_numericalDimension_zero_isNumericallyTrivial K k hk hkpos LZ HZ hLZ
      hHZ (hzero k hk LZ HZ aL hHZ)
    exact htriv C hC φW (comp_over φW (Spec (CommRingCat.of K)))

/-- **An isolated numerically trivial log canonical centre in a base locus.** For a normal
projective klt pair of dimension n ≥ 2, a nef D with (r a) D − D' nef and big, and a multiple
m D with a nonzero section and a nonempty base locus, there is a log canonical pair (d₃, D₃) whose
non-klt locus is exactly W = closure {η} ⊆ Bs(m D), with all large adjoints ample, such that D has
degree zero on every proper smooth curve mapping into W. -/
theorem klt_base_locus_exists_isolated_numericallyTrivial_center
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 2 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D) (a : ℕ)
    (hnef : CartierIsNef K ((r * a) • D - D')) (hbig : CartierIsBig K ((r * a) • D - D'))
    (m : ℕ) (s₀ : Γ((m • D).sheaf, ⊤)) (hs₀ : s₀ ≠ 0)
    (hbase : (cartierBaseLocus (m • D) : Set X).Nonempty) :
    ∃ (d₃ : ℕ) (_ : 1 ≤ d₃) (D₃ : CartierDivisor X) (η : X) (b₃ : ℕ),
      LogPairBoundaryEffective c₀ f₀ d₃ D₃ ∧ LogPairIsLogCanonical c₀ f₀ d₃ D₃ ∧
      LogPairIsLogCanonicalCenter c₀ f₀ d₃ D₃ ⟨closure {η}, isClosed_closure⟩ ∧
      (∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c₀ f₀ d₃ D₃) ↔ x ∈ closure {η}) ∧
      (∀ j : ℕ, b₃ ≤ j → CartierIsAmpleProj K ((d₃ * j) • D - D₃)) ∧
      closure {η} ⊆ (cartierBaseLocus (m • D) : Set X) ∧
      ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
        [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
        topologicalKrullDim C = 1 → ∀ (φ : C ⟶ X) [φ.IsOver (Spec (CommRingCat.of K))],
        Set.range φ ⊆ closure {η} → cartierCurvePullbackDegree (K := K) D φ = 0 := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  -- the base-source pair
  obtain ⟨s, hs2, G₀, hG₀, heff₁, hklt₁, hamp₁, a', q, N', ha', hq, hN', haq, t, ht, I, -, hIne, -,
    -, -, -, hIsupp, hInk, -, -⟩ :=
    original_klt_bpf_exists_base_source_ample_adjoints_and_Serre_lifting K hdim (by omega) hnorm
      hcov ⟨J, hJ⟩ c₀ f₀ r hr D' heff hklt D hD a hnef hbig m s₀ hs₀ hbase
  set d₁ := s * r with hd₁def
  set D₁ := s • D' + G₀ with hD₁def
  set Zt := cartierSectionZeroDivisor (N' • (m • D)) t ht with hZtdef
  have hZt : Zt.IsEffective := cartierSectionZeroDivisor_isEffective _ _ _
  have hd₁ : 1 ≤ d₁ := by
    have : 1 ≤ s := by omega
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- a point of the non-klt locus
  obtain ⟨y⟩ := hIne
  set x₀ := I.subschemeι y with hx₀
  have hx₀I : x₀ ∈ (I.support : Set X) := by
    rw [hx₀, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have hnk₀ := (hInk x₀).mp hx₀I
  have hq' : 1 ≤ q * N' := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hZt0 : Zt ≠ 0 := by
    intro h0
    apply hnk₀
    have hkltq : LogPairIsKlt c₀ f₀ ((q * N') * d₁) ((q * N') • D₁ + (d₁ * a') • Zt) := by
      rw [h0, smul_zero, add_zero]
      exact (logPairIsKlt_scale_denominator_iff c₀ f₀ d₁ (q * N') hq' D₁).mpr hklt₁
    exact logPairIsKlt_overBasePoint (𝟙 X) x₀ c₀ f₀ _ _ hkltq
  -- the exact rational threshold towards the base-source pair
  obtain ⟨a₂, q₂, ha₂, hq₂, -, hlc₂, hnot₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hiff⟩ :=
    exists_exact_rational_klt_perturbation_threshold hnorm c₀ f₀ d₁ hd₁ D₁ heff₁ hklt₁ Zt hZt hZt0
  set Dt := q₂ • D₁ + (d₁ * a₂) • Zt with hDtdef
  have hle₂ : (a₂ : ℚ) / q₂ ≤ (a' : ℚ) / (q * N' : ℕ) := by
    by_contra hlt
    rw [not_le] at hlt
    have hkltq := ((hiff a' (q * N') hq').2.1).mpr hlt
    exact hnk₀ (logPairIsKlt_overBasePoint (𝟙 X) x₀ c₀ f₀ _ _ hkltq)
  -- a minimal log canonical centre of the threshold pair lies in the base locus
  obtain ⟨W₀, hW₀, hW₀min⟩ := logCanonical_nonKlt_exists_minimal_center c₀ f₀ (q₂ * d₁) Dt hlc₂
    hnot₂
  have hW₀B : (W₀ : Set X) ⊆ (cartierBaseLocus (m • D) : Set X) := by
    intro x hx
    have hnk := logPairIsLogCanonicalCenter_not_kltOverBasePoint c₀ f₀ _ _ W₀ hW₀ x hx
    have hnk' : ¬ LogPairIsKltOverBasePoint (𝟙 X) x c₀ f₀ ((q * N') * d₁)
        ((q * N') • D₁ + (d₁ * a') • Zt) := fun hk =>
      hnk (logPairIsKltOverBasePoint_rational_perturbation_of_le c₀ f₀ d₁ D₁ Zt hZt a₂ q₂ a'
        (q * N') hq₂ hq' hle₂ x hk)
    exact hIsupp ((hInk x).mpr hnk')
  -- all large adjoints of the threshold pair are ample
  set bt := a + a₂ * N' * m with hbt
  have hampt : ∀ j : ℕ, bt ≤ j → CartierIsAmpleProj K ((q₂ * d₁ * j) • D - Dt) := by
    intro j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    have hkey : (q₂ * d₁ * (bt + i)) • D - Dt =
        ((((q₂ - 1) * (d₁ * a₂ * (N' * m)) + q₂ * d₁ * i) • D) +
          q₂ • ((d₁ * a) • D - D₁)) +
          principalCartierDivisor X ((cartierSectionUnit (N' • (m • D)) t ht ^ (d₁ * a₂))⁻¹) := by
      obtain ⟨q₃, rfl⟩ : ∃ q₃, q₂ = q₃ + 1 := ⟨q₂ - 1, by omega⟩
      rw [hDtdef, hZtdef, cartierSectionZeroDivisor, principalCartierDivisor_inv,
        principalCartierDivisor_power, hbt, Nat.add_sub_cancel]
      simp only [smul_add, smul_sub, smul_smul, add_smul, mul_add, add_mul, one_mul]
      module
    rw [hkey]
    apply cartierIsAmpleProj_add_principal
    exact proper_nef_add_ample_isAmpleProj K _ _ (cartierIsNef_nsmul hD _)
      (cartierIsAmpleProj_nsmul hamp₁ hq₂)
  have hdt : 1 ≤ q₂ * d₁ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- the minimal centre with numerically trivial restriction, and its isolation
  obtain ⟨d', b', hd', D'', η, hPη, heff'', hamp'', hWle, hlcW, hmin, hzero⟩ :=
    original_ample_adjoint_lc_center_contains_restricted_numerical_zero_endpoint K hn hnorm c₀ f₀
      D hD (q₂ * d₁) bt hdt Dt (hiff a₂ q₂ hq₂).1 hampt W₀ hW₀
  obtain ⟨d₃, hd₃, D₃, heff₃, hlc₃, hcent₃, hamp₃, -, hNK₃, -⟩ :=
    minimal_lc_center_arbitrary_klt_anchor_unique_center_isolation_and_original_lifting K
      (by omega) hnorm c₀ f₀ d' hd' D'' heff'' r hr D' heff hklt _ hlcW hmin D hD b'
      (hamp'' b' le_rfl)
  refine ⟨d₃, hd₃, D₃, η, b', heff₃, hlc₃, hcent₃, hNK₃, hamp₃, ?_, ?_⟩
  · exact fun x hx => hW₀B (hWle hx)
  · intro C _ _ _ _ hC φ _ hφ
    exact curve_into_pointClosure_pullbackDegree_eq_zero K ⟨J, hJ⟩ D hD η hzero C hC φ hφ

end MixedFujita
