/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothLemmaThreeCharZero
public import MixedFujita.IsolationExtractionPrime
public import MixedFujita.ProjectiveSNCModelPrincipalization
public import MixedFujita.CrepantBoundaryPerturbation
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.PrincipalizedIdealCoefficients
public import MixedFujita.RealizationThresholdReduction
public import MixedFujita.NormalCartierPowerRoot

/-!
Lemma 3 for klt pairs with effective boundary on a smooth variety, by absorbing the boundary into
the ideal (step 15).

A pair (Y, B) on a smooth variety is given by (c_Y, f_Y, d, D₀) with D₀ = d (K_Y + B) and
K_Y = div(f_Y dx) in the chart c_Y (check-1 conventions); its boundary is
E₀ = D₀ - d (K_Y + div f_Y) = d B (`pairBoundaryCartier`). On every smooth birational test model σ
the discrepancy divisor of the pair is d times that of the zero pair minus σ*E₀
(`logDiscrepancyDivisor_pair_eq`), so A_pair(e) = A(e) - ord_e(E₀)/d.

If B is effective and the pair is klt, then A_pair(e) > 0 for every prime e of every smooth
birational test model with A(e) > 0 (`logPair_testPrime_pos`): on a projective simple normal
crossing model principalizing E₀, the orders o_s of the members along e satisfy
d A_pair(e) ≥ Σ_s (d - b_s) o_s (check 307), with b_s < d by klt, and if all o_s vanish then
ord_e(E₀) = 0. Hence, for a local equation h of E₀ near x, the threshold of g for the pair is at
most 1/M exactly when the threshold of g^d h^M for the zero pair is at most 1/(d M)
(`modelThresholdBadAt_pair_iff`). With Lemma 3 for the zero pair (check 559) this gives Lemma 3 at
a closed point for the pair (`idealThresholdZariskiClosed_pair`) and the closedness of its
realization sets in the tuple (`realizationSetsZariskiClosed_pair`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Discrepancy

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- The boundary E₀ = D₀ - d (K_Y + div f_Y) = d B of the pair given by (c_Y, f_Y, d, D₀) on a
smooth variety. -/
noncomputable def pairBoundaryCartier (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ : CartierDivisor Y) : CartierDivisor Y :=
  D₀ - d • (smoothCanonicalDivisor cY + principalCartierDivisor Y fY)

variable {U : Scheme.{u}} [IsIntegral U] [U.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- **The discrepancy divisor of a pair on a smooth variety** is d times that of the zero pair
minus the pullback of the boundary. -/
theorem logDiscrepancyDivisor_pair_eq (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ : CartierDivisor Y) (cU : EtaleChart K U n) :
    logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover =
      d • logDiscrepancyDivisor n σ hσ cY 1 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU etaleCharts_cover -
        cartierPullback σ (pairBoundaryCartier cY fY d D₀) := by
  unfold logDiscrepancyDivisor pullbackFormDivisor pairBoundaryCartier
  rw [map_one, one_mul, principalCartierDivisor_mul, principalCartierDivisor_one, add_zero,
    one_nsmul, one_nsmul, cartierPullback_sub, cartierPullback_nsmul, cartierPullback_add,
    cartierPullback_principal]
  simp only [smul_sub, smul_add]
  abel

/-- The coefficients of the discrepancy divisor of a pair on a smooth variety. -/
theorem cartierCoefficient_logDiscrepancyDivisor_pair [IsLocallyNoetherian U] (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y) (cU : EtaleChart K U n) (e : U) :
    cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) e =
      d * cartierCoefficient (logDiscrepancyDivisor n σ hσ cY 1 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU etaleCharts_cover) e -
        cartierCoefficient (cartierPullback σ (pairBoundaryCartier cY fY d D₀)) e := by
  rw [logDiscrepancyDivisor_pair_eq σ hσ, cartierCoefficient_sub, cartierCoefficient_nsmul]

end Discrepancy

section Positivity

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- **A klt pair with effective boundary on a smooth variety has positive log discrepancy along
every prime of every smooth birational test model** (with positive log discrepancy for the zero
pair, which always holds). -/
theorem logPair_testPrime_pos (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) (cU : EtaleChart K U n)
    (e : CodimensionOnePoint U)
    (h0 : 0 < 1 + cartierCoefficient (logDiscrepancyDivisor n σ hσ cY 1 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU etaleCharts_cover)
        (e : U)) :
    0 < (d : ℤ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U) := by
  classical
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, hG, -, -, -, -, Gc, hGc, hGcI, hGc0, -, -⟩ :=
    exists_projective_snc_model_principalizing_sum (X := Y) cY fY d D₀
      (fun _ : Unit => pairBoundaryCartier cY fY d D₀) (fun _ : Unit => (0 : CartierDivisor Y))
      (fun _ => CartierDivisor.isEffective_zero) (Empty.elim : Empty → Y.IdealSheafData)
      (fun j => j.elim)
  have := hTi
  have := hTN
  have := hTs
  have := hdom
  have := hover
  have := hprop
  have hb : ∀ s, cartierCoefficient
      (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s) < d := by
    intro s
    have h1 := hklt T ρ hρ cT (ξ s) (hcoh s)
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
    linarith
  obtain ⟨o, -, -, ho0, -, hcoeff, -, hlog⟩ := exists_snc_orders_at_test_prime ρ hρ cY fY d D₀ cT
    ξ hinj hcoh hsnc hsupp (fun _ : Unit => (0 : CartierDivisor Y))
    (fun _ => CartierDivisor.isEffective_zero) Gc hGc hGc0 hGcI σ hσ cU e
  by_cases hall : ∀ s, o s = 0
  · have hE0 : cartierCoefficient (cartierPullback σ (pairBoundaryCartier cY fY d D₀)) (e : U) =
        0 := by
      rw [hcoeff _ (hG ())]
      simp [hall]
    rw [cartierCoefficient_logDiscrepancyDivisor_pair σ hσ, hE0, sub_zero]
    have hd' : (0 : ℤ) < d := by exact_mod_cast hd
    nlinarith
  · push Not at hall
    obtain ⟨s₀, hs₀⟩ := hall
    have hpos : 0 < ∑ s, ((d : ℤ) - cartierCoefficient
        (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s)) * o s := by
      apply Finset.sum_pos' (fun s _ => mul_nonneg (by linarith [hb s]) (ho0 s))
      exact ⟨s₀, Finset.mem_univ _,
        mul_pos (by linarith [hb s₀]) (lt_of_le_of_ne (ho0 s₀) (Ne.symm hs₀))⟩
    have hsum : ∑ s, ((d : ℤ) - cartierCoefficient
        (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s)) * o s =
        (d : ℤ) * ∑ s, o s - ∑ s, cartierCoefficient
          (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s) * o s := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    linarith

omit [CharZero K] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))] in
/-- Along a prime of a test model whose image specializes to a point of an open set on which h is
a local equation of the boundary, the coefficient of the pulled back boundary is the order of the
pulled back h, and it is nonnegative for an effective boundary. -/
theorem pairBoundary_testPrime_coefficient (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ : CartierDivisor Y) (hE : (pairBoundaryCartier cY fY d D₀).IsEffective)
    (x : Y) (V : Y.Opens) (hxV : x ∈ V) (h : Y.functionFieldˣ)
    (hloc : ∀ y ∈ V, (pairBoundaryCartier cY fY d D₀).IsLocalEquationAt y h)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [U.Over (Spec (CommRingCat.of K))]
    (σ : U ⟶ Y) [IsDominant σ] (e : U) (hx : x ∈ closure ({σ e} : Set Y)) :
    cartierCoefficient (cartierPullback σ (pairBoundaryCartier cY fY d D₀)) e =
        U.ord ((dominantFunctionFieldMap σ).hom (h : Y.functionField)) e ∧
      0 ≤ cartierCoefficient (cartierPullback σ (pairBoundaryCartier cY fY d D₀)) e := by
  have hV : σ e ∈ V := (specializes_iff_mem_closure.mpr hx).mem_open V.isOpen hxV
  have h1 := cartierPullback_isLocalEquationAt σ (pairBoundaryCartier cY fY d D₀) e
    (hloc (σ e) hV)
  refine ⟨?_, cartierCoefficient_nonneg_of_isEffective _
    (cartierPullback_isEffective σ _ hE) e⟩
  rw [cartierCoefficient_eq_ord h1]
  rfl

/-- **Absorbing the boundary**: for a klt pair with effective boundary on a smooth variety and a
local equation h of the boundary near x, the threshold of g for the pair is at most 1/M exactly
when the threshold of g^d h^M for the zero pair is at most 1/(d M). -/
theorem modelThresholdBadAt_pair_iff (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (hE : (pairBoundaryCartier cY fY d D₀).IsEffective) (x : Y) (V : Y.Opens) (hxV : x ∈ V)
    (h : Y.functionFieldˣ)
    (hloc : ∀ y ∈ V, (pairBoundaryCartier cY fY d D₀).IsLocalEquationAt y h)
    {J : Type*} (g : J → Y.functionField) (M : ℕ) :
    ModelThresholdBadAt cY fY d D₀ x g M ↔
      ModelThresholdBadAt cY 1 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) x
        (fun j => g j ^ d * (h : Y.functionField) ^ M) (d * M) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hne : ∀ j, g j ^ d * (h : Y.functionField) ^ M ≠ 0 ↔ g j ≠ 0 := by
    intro j
    constructor
    · intro hj hg
      apply hj
      rw [hg, zero_pow (by omega), zero_mul]
    · intro hg
      exact mul_ne_zero (pow_ne_zero _ hg) (pow_ne_zero _ (Units.ne_zero h))
  constructor
  · rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, hpos, hineq⟩
    have := hUi
    have := hUn
    obtain ⟨hcE, hcE0⟩ := pairBoundary_testPrime_coefficient cY fY d D₀ hE x V hxV h hloc σ
      (e : U) hx
    have hcp := cartierCoefficient_logDiscrepancyDivisor_pair σ hσ cY fY d D₀ cU (e : U)
    refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, ?_, ?_⟩
    · have hcp' : ((cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU
          etaleCharts_cover) (e : U) : ℤ) : ℝ) = d * (cartierCoefficient (logDiscrepancyDivisor n
            σ hσ cY 1 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU
            etaleCharts_cover) (e : U) : ℝ) - (cartierCoefficient (cartierPullback σ
            (pairBoundaryCartier cY fY d D₀)) (e : U) : ℝ) := by
        rw [hcp]
        push_cast
        ring
      have hc0 : (0 : ℝ) ≤ (cartierCoefficient (cartierPullback σ
          (pairBoundaryCartier cY fY d D₀)) (e : U) : ℝ) := by exact_mod_cast hcE0
      rw [hcp', lt_div_iff₀ hdR] at hpos
      simp only [Nat.cast_one, div_one]
      nlinarith
    · intro j hj
      have hgj : g j ≠ 0 := (hne j).mp hj
      have hgj' : (dominantFunctionFieldMap σ).hom (g j) ≠ 0 :=
        (map_ne_zero ((dominantFunctionFieldMap σ).hom)).mpr hgj
      have hh' : (dominantFunctionFieldMap σ).hom (h : Y.functionField) ≠ 0 :=
        (map_ne_zero ((dominantFunctionFieldMap σ).hom)).mpr (Units.ne_zero h)
      have hord : U.ord ((dominantFunctionFieldMap σ).hom (g j ^ d * (h : Y.functionField) ^ M))
          (e : U) = d * U.ord ((dominantFunctionFieldMap σ).hom (g j)) (e : U) +
            M * U.ord ((dominantFunctionFieldMap σ).hom (h : Y.functionField)) (e : U) := by
        rw [map_mul, map_pow, map_pow, U.ord_mul (pow_ne_zero _ hgj') (pow_ne_zero _ hh'),
          scheme_ord_pow_of_ne_zero _ hgj', scheme_ord_pow_of_ne_zero _ hh']
      have h1 := hineq j hgj
      rw [hord]
      rw [← hcE] at hord ⊢
      have hcp' : ((cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU
          etaleCharts_cover) (e : U) : ℤ) : ℝ) = d * (cartierCoefficient (logDiscrepancyDivisor n
            σ hσ cY 1 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU
            etaleCharts_cover) (e : U) : ℝ) - (cartierCoefficient (cartierPullback σ
            (pairBoundaryCartier cY fY d D₀)) (e : U) : ℝ) := by
        rw [hcp]
        push_cast
        ring
      rw [hcp'] at h1
      simp only [Nat.cast_one, div_one]
      push_cast
      set a : ℝ := (cartierCoefficient (logDiscrepancyDivisor n σ hσ cY 1 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU etaleCharts_cover)
        (e : U) : ℝ)
      set c : ℝ := (cartierCoefficient (cartierPullback σ (pairBoundaryCartier cY fY d D₀))
        (e : U) : ℝ)
      set o : ℝ := (U.ord ((dominantFunctionFieldMap σ).hom (g j)) (e : U) : ℝ)
      have key : (M : ℝ) * ((d + (d * a - c)) / d) = (d * M * (1 + a) - M * c) / d := by
        field_simp
        ring
      rw [key, div_le_iff₀ hdR] at h1
      linarith
  · rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, hpos, hineq⟩
    have := hUi
    have := hUn
    obtain ⟨hcE, hcE0⟩ := pairBoundary_testPrime_coefficient cY fY d D₀ hE x V hxV h hloc σ
      (e : U) hx
    have hcp := cartierCoefficient_logDiscrepancyDivisor_pair σ hσ cY fY d D₀ cU (e : U)
    simp only [Nat.cast_one, div_one] at hpos
    have h0 : 0 < 1 + cartierCoefficient (logDiscrepancyDivisor n σ hσ cY 1 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU etaleCharts_cover)
          (e : U) := by exact_mod_cast hpos
    have hpp := logPair_testPrime_pos cY fY hd D₀ hklt σ hσ cU e h0
    refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, ?_, ?_⟩
    · apply div_pos _ hdR
      exact_mod_cast hpp
    · intro j hgj
      have hj : g j ^ d * (h : Y.functionField) ^ M ≠ 0 := (hne j).mpr hgj
      have hgj' : (dominantFunctionFieldMap σ).hom (g j) ≠ 0 :=
        (map_ne_zero ((dominantFunctionFieldMap σ).hom)).mpr hgj
      have hh' : (dominantFunctionFieldMap σ).hom (h : Y.functionField) ≠ 0 :=
        (map_ne_zero ((dominantFunctionFieldMap σ).hom)).mpr (Units.ne_zero h)
      have hord : U.ord ((dominantFunctionFieldMap σ).hom (g j ^ d * (h : Y.functionField) ^ M))
          (e : U) = d * U.ord ((dominantFunctionFieldMap σ).hom (g j)) (e : U) +
            M * U.ord ((dominantFunctionFieldMap σ).hom (h : Y.functionField)) (e : U) := by
        rw [map_mul, map_pow, map_pow, U.ord_mul (pow_ne_zero _ hgj') (pow_ne_zero _ hh'),
          scheme_ord_pow_of_ne_zero _ hgj', scheme_ord_pow_of_ne_zero _ hh']
      have h1 := hineq j hj
      rw [hord, ← hcE] at h1
      simp only [Nat.cast_one, div_one] at h1
      push_cast at h1
      have hcp' : ((cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU
          etaleCharts_cover) (e : U) : ℤ) : ℝ) = d * (cartierCoefficient (logDiscrepancyDivisor n
            σ hσ cY 1 1 (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU
            etaleCharts_cover) (e : U) : ℝ) - (cartierCoefficient (cartierPullback σ
            (pairBoundaryCartier cY fY d D₀)) (e : U) : ℝ) := by
        rw [hcp]
        push_cast
        ring
      rw [hcp']
      set a : ℝ := (cartierCoefficient (logDiscrepancyDivisor n σ hσ cY 1 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y 1)) cU etaleCharts_cover)
        (e : U) : ℝ)
      set c : ℝ := (cartierCoefficient (cartierPullback σ (pairBoundaryCartier cY fY d D₀))
        (e : U) : ℝ)
      set o : ℝ := (U.ord ((dominantFunctionFieldMap σ).hom (g j)) (e : U) : ℝ)
      have key : (M : ℝ) * ((d + (d * a - c)) / d) = (d * M * (1 + a) - M * c) / d := by
        field_simp
        ring
      rw [key, div_le_iff₀ hdR]
      linarith

end Positivity

section Point

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- **Lemma 3 at a closed point for a klt pair with effective boundary on a smooth variety**, in
characteristic zero. -/
theorem idealThresholdZariskiClosed_pair (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (hE : (pairBoundaryCartier cY fY d D₀).IsEffective) (x : Y) (hx : IsClosed ({x} : Set Y)) :
    IdealThresholdZariskiClosed cY fY d D₀ x := by
  classical
  intro ι J _ _ G M hM
  obtain ⟨f, hf, a, ha⟩ : ∃ f : Y.functionFieldˣ,
      (pairBoundaryCartier cY fY d D₀).IsLocalEquationAt x f ∧
        ∃ a : Y.presheaf.stalk x, algebraMap (Y.presheaf.stalk x) Y.functionField a =
          (f : Y.functionField) := by
    obtain ⟨f, hf, ⟨a, ha⟩⟩ := CartierDivisor.isEffective_iff_exists.mp hE x
    exact ⟨f, hf, a, ha⟩
  obtain ⟨V, hxV, hV⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have hloc : ∀ y ∈ V, (pairBoundaryCartier cY fY d D₀).IsLocalEquationAt y f := by
    intro y hy
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV hy
  let G' : J → MvPolynomial ι (Y.presheaf.stalk x) := fun j => G j ^ d * MvPolynomial.C a ^ M
  obtain ⟨I, hI⟩ := idealThresholdZariskiClosed_of_charZero cY x hx G' (d * M) (by nlinarith)
  refine ⟨I, ?_⟩
  rw [← hI]
  ext c
  simp only [Set.mem_ofPred_eq]
  have hinj := IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
  have heval : ∀ j, algebraMap (Y.presheaf.stalk x) Y.functionField
      (MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G' j)) =
      (algebraMap (Y.presheaf.stalk x) Y.functionField
        (MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G j))) ^ d *
        (f : Y.functionField) ^ M := by
    intro j
    simp only [G', map_mul, map_pow, MvPolynomial.eval_C, ha]
  have hzero : ∀ j, MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G' j) ≠
      0 ↔ algebraMap (Y.presheaf.stalk x) Y.functionField
        (MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G' j)) ≠ 0 :=
    fun j => (map_ne_zero_iff _ hinj).symm
  have hzero' : ∀ j, MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G j) ≠
      0 ↔ algebraMap (Y.presheaf.stalk x) Y.functionField
        (MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G j)) ≠ 0 :=
    fun j => (map_ne_zero_iff _ hinj).symm
  have hiff := modelThresholdBadAt_pair_iff cY fY hd D₀ hklt hE x V hxV f hloc
    (fun j => algebraMap (Y.presheaf.stalk x) Y.functionField
      (MvPolynomial.eval (fun i => algebraMap K (Y.presheaf.stalk x) (c i)) (G j))) M
  unfold ModelThresholdBadAt at hiff
  simp only [hzero, hzero', heval]
  exact hiff

/-- **The closedness of the realization sets in the tuple at a closed point**, for a klt pair with
effective boundary on a smooth variety, in characteristic zero. -/
theorem realizationSetsZariskiClosed_pair (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (hE : (pairBoundaryCartier cY fY d D₀).IsEffective) (x : Y) (hx : IsClosed ({x} : Set Y))
    (D : CartierDivisor Y) : RealizationSetsZariskiClosed cY fY d D₀ D x :=
  realizationSetsZariskiClosed_of_idealThreshold cY fY d D₀ x
    (idealThresholdZariskiClosed_pair cY fY hd D₀ hklt hE x hx) D

end Point

end MixedFujita
