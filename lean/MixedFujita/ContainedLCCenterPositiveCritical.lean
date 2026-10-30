/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.DVRSupportPositiveCartierCoefficient
public import MixedFujita.LogCanonicalCenters
public import MixedFujita.FiniteCompleteCartierBaseIdeal
public import MixedFujita.PrincipalizedIdealCoefficients
public import MixedFujita.PositiveRationalLCThreshold

/-! 中心包含Mの全正摂動非lcと任意SNCモデルの旧臨界正係数。 See reports/check-268-internal-lc-center-isolation.json for the verified scope. ACTUAL minimal-lc-center isolation now internally constructs the original center ideal finite system, SAME-original-family principalization/residual Bertini, source perturbation, shared SNC model, old-critical positivity and placement. A contained lc center obstructs every positive perturbation, forcing a positive old-critical coefficient on ANY joint model by finite-LC-threshold contradiction. Arbitrary anchor denominators are normalized retaining actual centers. Original positive-numerical klt BPF assumptions construct an isolated restricted-numerical-zero center; EXPLICIT usual H1 KV gives exact-center original mL lifting. Zero-dimensional minimal centers yield original nonvanishing under usual KV. Positive-dimensional numerical-zero-center nonvanishing, general KV, the original nu=0 branch, unconditional BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- An ACTUAL lc center contained in an ACTUAL effective Cartier divisor
obstructs EVERY positive rational perturbation. The actual discrepancy prime
is extracted from the center itself; no test model or positive order is supplied. -/
theorem lc_center_contained_effective_divisor_obstructs_positive_perturbation
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (M : CartierDivisor X) (hM : M.IsEffective)
    (hcontain : Z ≤ (effectiveCartierIdealSheaf M hM).support)
    (p q : ℕ) (hp : 1 ≤ p) (_hq : 1 ≤ q) :
    ¬ LogPairIsLogCanonical c f (q * d) (q • D + (d * p) • M) := by
  obtain ⟨_, T, hTi, hTN, hTo, hTs, ρ, hdom, hover, hproper, hρ, cT, t, ht, hdiscr, hset⟩ := hZ
  let := hTi
  let := hTN
  let := hTo
  let := hTs
  let := hdom
  let := hover
  let := hproper
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) (⟨t, ht⟩ : CodimensionOnePoint T)
  have himage : ρ t ∈ Z := by
    change ρ t ∈ (Z : Set X)
    rw [hset]
    exact subset_closure rfl
  have hup : t ∈ (effectiveCartierIdealSheaf (cartierPullback ρ M) (cartierPullback_isEffective ρ M hM)).support := by
    rw [effectiveCartierIdealSheaf_cartierPullback ρ M hM, Scheme.IdealSheafData.support_comap]
    exact hcontain himage
  have hpos := effective_cartier_coefficient_pos_of_mem_support_at_dvr
    (cartierPullback ρ M) (cartierPullback_isEffective ρ M hM) ⟨t, ht⟩ hup
  intro hnew
  have hh := hnew T ρ hρ cT t ht
  rw [logDiscrepancyDivisor_add_source, logDiscrepancyDivisor_scale_denominator,
    cartierPullback_nsmul, cartierCoefficient_sub, cartierCoefficient_nsmul,
    cartierCoefficient_nsmul, hdiscr] at hh
  have hprod : 0 < ((d * p : ℕ) : ℤ) * cartierCoefficient (cartierPullback ρ M) t :=
    mul_pos (by exact_mod_cast Nat.mul_pos (by omega : 0 < d) (by omega : 0 < p)) hpos
  push_cast at hh hprod
  nlinarith


/-- EVERY actual joint SNC model has an OLD critical prime with positive
perturbation whenever the actual effective divisor contains an actual lc center.
An arbitrary model need not be assumed to retain the center's given prime:
otherwise a finite positive LC threshold would contradict its original witness. -/
theorem lc_center_contained_effective_divisor_forces_snc_positive_critical_prime
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (M : CartierDivisor X) (hM : M.IsEffective) (hcontain : Z ≤ (effectiveCartierIdealSheaf M hM).support)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppD : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (z : T) = 0)
    (hsuppM : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ M) (z : T) = 0) :
    ∃ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = d ∧
      0 < cartierCoefficient (cartierPullback ρ M) (ξ i) := by
  classical
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) := fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hne : M ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := (logPairIsLogCanonicalCenter_isIrreducible c f d D Z hZ).nonempty
    have hh := hcontain hx
    subst M
    rw [effectiveCartierIdealSheaf_zero_eq_top hM, Scheme.IdealSheafData.support_top] at hh
    exact hh
  obtain ⟨z, hz⟩ := proper_birational_effective_pullback_exists_positive_prime hnorm hnormT ρ hρ M hM hne
  have hin : (z : T) ∈ Set.range ξ := by
    by_contra hnot
    rw [hsuppM z hnot] at hz
    exact lt_irrefl _ hz
  obtain ⟨i, hi⟩ := hin
  let β := fun i => cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i)
  let g := fun i => cartierCoefficient (cartierPullback ρ M) (ξ i)
  have hb (i : Fin r) : β i ≤ (d : ℤ) :=
    logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hZ.1 cT ⟨ξ i, hξ i⟩
  have hg (i : Fin r) : 0 ≤ g i := cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ M hM) (ξ i)
  have hgpos : ∃ i, 0 < g i := ⟨i, by simpa only [g, hi] using hz⟩
  by_contra hno
  have hcritical (i : Fin r) (hbi : β i = (d : ℤ)) : g i = 0 := by
    have hnp : ¬ 0 < g i := fun hgi => hno ⟨i, hbi, hgi⟩
    have := hg i
    omega
  obtain ⟨a, q, _, ha, hq, _, _, _, _, htest⟩ := finite_integer_lc_coefficients_exact_threshold β g d hd hb hg hcritical hgpos
  have hlc' : LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • M) :=
    (logPairIsLogCanonical_rational_perturbation_iff_snc_coefficients ρ hρ c f d hd D M cT ξ hinj hξ hsnc
      hsuppD hsuppM a q hq).mpr ((htest a q hq).mpr le_rfl)
  exact lc_center_contained_effective_divisor_obstructs_positive_perturbation c f d hd D Z hZ M hM hcontain a q ha hq hlc'

end MixedFujita
