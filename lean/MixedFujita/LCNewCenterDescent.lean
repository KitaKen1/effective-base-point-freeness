/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PositiveRationalLCThreshold
public import MixedFujita.LogCanonicalDenominatorScaling
public import MixedFujita.CartierSectionPullbackAvoidance
public import MixedFujita.IsolationRationalData

/-! discrepancy凸性と実非lc集中による条件付き真部分中心。 See reports/check-257-lc-threshold-subcenter-descent.json for the verified scope. Original lc pairs with a nonzero effective divisor avoiding all old actual lc centers have an internally constructed exact positive rational threshold and a new actual lc center. Discrepancy convexity confines a new center to the prescribed closed set if a larger coefficient is lc outside it. An actual non-lc point, old-center avoidance and exterior lc imply a strict new subcenter. Canonical reduced strict subcenters have strictly smaller ordinary Krull dimension, using an internally constructed closed immersion. These are conditional criteria: the Bertini divisor and actual ambient non-lc point from restricted concentration are not yet constructed. Center normality, center classification, general KV, original L nonvanishing and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower


/-- A new lc center at a STRICTLY smaller coefficient is contained in the
prescribed closed set if the larger perturbation is lc outside that set.
This is an all-model discrepancy convexity argument, without SNC or normality. -/
theorem strict_lc_perturbation_new_center_le_closed_of_lc_outside
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d a q j : ℕ)
    (hsmall : d * a * j < q) (D M : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (houtside : ∀ x : X, x ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M))
    (W : Closeds X) (hW : LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) W)
    (hnotOld : ¬ LogPairIsLogCanonicalCenter c f d D W) : W ≤ Z := by
  classical
  obtain ⟨_, T, _, _, _, _, ρ, _, _, _, hρ, cT, t, ht, heq, hset⟩ := hW
  intro x hxW
  by_contra hxZ
  have hxcl : x ∈ closure ({(ρ ≫ 𝟙 X) t} : Set X) := by
    change x ∈ (W : Set X) at hxW
    simpa only [Category.comp_id, hset] using hxW
  have hlarge := houtside x hxZ T ρ hρ cT t ht hxcl
  have hold := hlc T ρ hρ cT t ht
  rw [logDiscrepancyDivisor_rational_perturbation, cartierCoefficient_sub,
    cartierCoefficient_nsmul, cartierCoefficient_nsmul] at heq
  rw [logDiscrepancyDivisor_add_source, logDiscrepancyDivisor_scale_denominator,
    cartierCoefficient_sub, cartierCoefficient_nsmul] at hlarge
  let A := cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT etaleCharts_cover) t
  let m := cartierCoefficient (cartierPullback ρ M) t
  have hA : A = -(d : ℤ) := by
    change -(d : ℤ) ≤ A at hold
    change -((j * d : ℕ) : ℤ) ≤ (j : ℤ) * A - m at hlarge
    change (q : ℤ) * A - ((d * a : ℕ) : ℤ) * m = -((q * d : ℕ) : ℤ) at heq
    have hsmallZ : (d : ℤ) * a * j < q := by exact_mod_cast hsmall
    have hmul := mul_le_mul_of_nonneg_left hlarge (show (0 : ℤ) ≤ (d : ℤ) * a by positivity)
    push_cast at heq hmul
    by_contra hn
    have hpos : 0 < A + d := by omega
    have hh := mul_pos (sub_pos.mpr hsmallZ) hpos
    nlinarith
  apply hnotOld
  exact ⟨hlc, T, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
    inferInstance, inferInstance, inferInstance, hρ, cT, t, ht, hA, hset⟩


/-- Concentration for an ORIGINAL lc pair, with actual center avoidance and
lc control outside an old center, constructs a strictly smaller NEW lc center.
The positive rational threshold, nonzero perturbation, endpoint and strict
coefficient bound are all internal. This criterion does not construct the
Bertini perturbation or the non-lc point supplied in its hypotheses. -/
theorem lc_concentration_exists_strictly_smaller_new_center
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hlc : LogPairIsLogCanonical c f d D) (M : CartierDivisor X) (hM : M.IsEffective)
    (havoid : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V →
      ¬ V ≤ (effectiveCartierIdealSheaf M hM).support)
    (j : ℕ) (hj : 1 ≤ j) (x : X)
    (hnonLC : ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M))
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (houtside : ∀ y : X, y ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) y c f (j * d) (j • D + M)) :
    ∃ a q : ℕ, 1 ≤ a ∧ 1 ≤ q ∧ d * a * j < q ∧
      LogPairBoundaryEffective c f (q * d) (q • D + (d * a) • M) ∧
      LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • M) ∧
      (¬ LogPairIsKlt c f (q * d) (q • D + (d * a) • M)) ∧
      ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) W ∧
        W < Z ∧ W ≤ (effectiveCartierIdealSheaf M hM).support ∧
          ¬ LogPairIsLogCanonicalCenter c f d D W := by
  have hjd : 1 ≤ j * d := Nat.mul_pos (by omega) (by omega)
  have hne : M ≠ 0 := by
    intro hzero
    have h := (logPairIsLogCanonical_scale_denominator_iff c f d j hj D).mpr hlc
    apply hnonLC
    rw [hzero, add_zero]
    exact logPairIsLogCanonical_overBasePoint (𝟙 X) x c f (j * d) (j • D) h
  obtain ⟨a, q, ha, hq, _, hLc, hnot, htest, W, hW, hWM, hnotOld⟩ :=
    exists_exact_positive_rational_lc_threshold_with_new_center hnorm c f d hd D hlc M hM hne havoid
  have hbad : ¬ LogPairIsLogCanonical c f ((j * d) * d)
      ((j * d) • D + (d * 1) • M) := by
    intro h
    apply hnonLC
    apply logPairIsLogCanonical_overBasePoint (𝟙 X) x c f (j * d) (j • D + M)
    apply (logPairIsLogCanonical_scale_denominator_iff c f (j * d) d hd (j • D + M)).mp
    have hpres : d • (j • D + M) = (j * d) • D + (d * 1) • M := by
      simp only [smul_add, smul_smul, mul_one, Nat.mul_comm]
    rwa [Nat.mul_comm d (j * d), hpres]
  have hratio : (a : ℚ) / q < (1 : ℚ) / (j * d : ℕ) := by
    apply lt_of_not_ge
    exact fun h => hbad ((htest 1 (j * d) hjd).mpr h)
  have hcross := (div_lt_div_iff₀ (by exact_mod_cast hq : (0 : ℚ) < q)
    (by exact_mod_cast hjd : (0 : ℚ) < (j * d : ℕ))).mp hratio
  have hprod : d * a * j < q := by
    have hcross' : (a : ℚ) * (j * d : ℕ) < q := by simpa only [one_mul] using hcross
    have hp : a * (j * d) < q := by exact_mod_cast hcross'
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hp
  have heffq := (logPairBoundaryEffective_scale_denominator_iff c f d q hq D).mpr heff
  have hle := strict_lc_perturbation_new_center_le_closed_of_lc_outside c f d a q j hprod D M hlc
    Z houtside W hW hnotOld
  have hlt : W < Z := lt_of_le_of_ne hle (fun heq => hnotOld (heq ▸ hZ))
  exact ⟨a, q, ha, hq, hprod,
    logPairBoundaryEffective_add_effective c f (q * d) _ _ heffq
      (cartier_nsmul_isEffective M hM (d * a)), hLc, hnot, W, hW, hlt, hWM, hnotOld⟩

end MixedFujita
