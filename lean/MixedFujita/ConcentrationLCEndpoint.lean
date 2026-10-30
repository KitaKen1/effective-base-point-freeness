/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalDenominatorScaling
public import MixedFujita.SignedRationalKltPerturbationThreshold
public import MixedFujita.LogPairOverBasePoint
public import MixedFujita.IsolationRationalData

/-! 非lc集中から厳密に小さい有効lc非klt実有理端点。 See reports/check-254-positive-numerical-lc-ample-source.json for the verified scope. Actual non-lc concentration internally gives a strictly smaller rational effective lc non-klt endpoint. Actual Cartier decomposition preserves an ample original L-adjoint in every large degree. Original normal klt BPF data with positive original numerical dimension construct a canonical nonempty reduced lower-dimensional non-klt source without an initial L section or KV; codimension-one charts follow internally from normality. The same source has all-large-original-L restriction lifting under explicit usual H1 KV. Initial and positive-dimensional restricted nonvanishing, minimal lc-center geometry, center-exterior control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- A concentrated EFFECTIVE non-lc perturbation constructs a genuine rational
lc non-klt endpoint STRICTLY below its normalized concentration coefficient.
The actual SNC threshold and a nonzero effective divisor are internal. -/
theorem effective_nonLC_concentration_exists_strictly_smaller_lc_endpoint
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) (M : CartierDivisor X) (hM : M.IsEffective)
    (j : ℕ) (hj : 1 ≤ j) (x : X)
    (hnonLC : ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d) (j • D + M)) :
    ∃ a q : ℕ, 1 ≤ a ∧ 1 ≤ q ∧ d * a * j < q ∧
      LogPairBoundaryEffective c f (q * d) (q • D + (d * a) • M) ∧
      LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • M) ∧
      ¬ LogPairIsKlt c f (q * d) (q • D + (d * a) • M) := by
  have hjd : 1 ≤ j * d := Nat.mul_pos (by omega) (by omega)
  have hne : M ≠ 0 := by
    intro hzero
    have hk := (logPairIsKlt_scale_denominator_iff c f d j hj D).mpr hklt
    apply hnonLC
    rw [hzero, add_zero]
    exact logPairIsKltOverBasePoint_logCanonical (𝟙 X) x c f (j * d) (j • D)
      (logPairIsKlt_overBasePoint (𝟙 X) x c f (j * d) (j • D) hk)
  obtain ⟨a, q, ha, hq, _, hlc, hnot, htest⟩ :=
    exists_exact_rational_signed_klt_perturbation_threshold hnorm c f d hd D hklt M hM hne
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
    intro h
    exact hbad ((htest 1 (j * d) hjd).2.mpr h)
  have hcross := (div_lt_div_iff₀ (by exact_mod_cast hq : (0 : ℚ) < q)
    (by exact_mod_cast hjd : (0 : ℚ) < (j * d : ℕ))).mp hratio
  have hprod : d * a * j < q := by
    have hcross' : (a : ℚ) * (j * d : ℕ) < q := by simpa only [one_mul] using hcross
    have hp : a * (j * d) < q := by exact_mod_cast hcross'
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hp
  have heffq := (logPairBoundaryEffective_scale_denominator_iff c f d q hq D).mpr heff
  exact ⟨a, q, ha, hq, hprod,
    logPairBoundaryEffective_add_effective c f (q * d) _ _ heffq
      (cartier_nsmul_isEffective M hM (d * a)), hlc, hnot⟩

end MixedFujita
