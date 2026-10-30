/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperCrepantBasePointInvariance
public import MixedFujita.SubKltBasePrimeRationalThreshold

/-!
Exact rational klt/lc tests and their finite endpoints are preserved by proper crepant
source modifications. This compares the actual perturbed divisors and actual pulled top
forms, without requiring effectivity of either crepant boundary.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral Y]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of K))]
  [IsSeparated (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (g : X ⟶ Y) [IsDominant g] (η : Y)

/-- Every nonnegative rational klt perturbation test is preserved on the actual proper
crepant source model, including its denominator and base Cartier pullback. -/
theorem rational_klt_overBasePoint_iff_proper_crepant_pullback
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (cT : EtaleChart K T n)
    (p q : ℕ) (hq : 1 ≤ q) :
    LogPairIsKltOverBasePoint g η c f (q * d)
      (q • D + (d * p) • cartierPullback g H) ↔
    LogPairIsKltOverBasePoint (ρ ≫ g) η cT (crepantPullbackFormUnit ρ hρ c f cT) (q * d)
      (q • cartierPullback ρ D + (d * p) • cartierPullback (ρ ≫ g) H) := by
  have hqd : 1 ≤ q * d := Nat.mul_pos (by omega) (by omega)
  simpa only [cartierPullback_add, cartierPullback_nsmul, ← cartierPullback_comp] using
    logPairIsKltOverBasePoint_iff_proper_crepant_pullback ρ hρ g η c f (q * d) hqd
      (q • D + (d * p) • cartierPullback g H) cT

/-- The non-strict lc endpoint tests are preserved by the same proper crepant model. -/
theorem rational_logCanonical_overBasePoint_iff_proper_crepant_pullback
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (cT : EtaleChart K T n)
    (p q : ℕ) (hq : 1 ≤ q) :
    LogPairIsLogCanonicalOverBasePoint g η c f (q * d)
      (q • D + (d * p) • cartierPullback g H) ↔
    LogPairIsLogCanonicalOverBasePoint (ρ ≫ g) η cT (crepantPullbackFormUnit ρ hρ c f cT) (q * d)
      (q • cartierPullback ρ D + (d * p) • cartierPullback (ρ ≫ g) H) := by
  have hqd : 1 ≤ q * d := Nat.mul_pos (by omega) (by omega)
  simpa only [cartierPullback_add, cartierPullback_nsmul, ← cartierPullback_comp] using
    logPairIsLogCanonicalOverBasePoint_iff_proper_crepant_pullback ρ hρ g η c f (q * d) hqd
      (q • D + (d * p) • cartierPullback g H) cT

/-- Exact finite rational endpoints computed before and after a proper crepant source
modification agree. Both interval descriptions refer to the actual all-model tests. -/
theorem rational_klt_threshold_eq_of_proper_crepant_pullback
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (cT : EtaleChart K T n)
    (a b q₀ s₀ : ℕ) (hq₀ : 1 ≤ q₀) (hs₀ : 1 ≤ s₀)
    (ha : ∀ (p q : ℕ), 1 ≤ q →
      (LogPairIsKltOverBasePoint g η c f (q * d)
        (q • D + (d * p) • cartierPullback g H) ↔ (p : ℚ) / q < (a : ℚ) / q₀))
    (hb : ∀ (p q : ℕ), 1 ≤ q →
      (LogPairIsKltOverBasePoint (ρ ≫ g) η cT (crepantPullbackFormUnit ρ hρ c f cT) (q * d)
        (q • cartierPullback ρ D + (d * p) • cartierPullback (ρ ≫ g) H) ↔
          (p : ℚ) / q < (b : ℚ) / s₀)) :
    (a : ℚ) / q₀ = (b : ℚ) / s₀ := by
  have htest (p q : ℕ) (hq : 1 ≤ q) :
      (p : ℚ) / q < (a : ℚ) / q₀ ↔ (p : ℚ) / q < (b : ℚ) / s₀ :=
    (ha p q hq).symm.trans
      ((rational_klt_overBasePoint_iff_proper_crepant_pullback ρ hρ g η c f d hd D H cT
        p q hq).trans (hb p q hq))
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact (lt_irrefl _) ((htest a q₀ hq₀).mpr hab)
  · exact (lt_irrefl _) ((htest b s₀ hs₀).mp hba)

/-- Finite base-prime thresholds exist directly on every proper crepant source model of a
klt pair, even when that model's boundary has negative coefficients. -/
theorem exists_exact_rational_base_prime_threshold_on_proper_crepant_model
    [IsLocallyNoetherian Y] [IsProper g] (θ : CodimensionOnePoint Y)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (H : CartierDivisor Y) (hH : H.IsEffective)
    (hθ : 0 < cartierCoefficient H (θ : Y)) (cT : EtaleChart K T n) :
    ∃ (a q₀ : ℕ), 1 ≤ a ∧ 1 ≤ q₀ ∧ ∀ (p q : ℕ), 1 ≤ q →
      (LogPairIsKltOverBasePoint (ρ ≫ g) (θ : Y) cT
        (crepantPullbackFormUnit ρ hρ c f cT) (q * d)
        (q • cartierPullback ρ D + (d * p) • cartierPullback (ρ ≫ g) H) ↔
          (p : ℚ) / q < (a : ℚ) / q₀) ∧
      (LogPairIsLogCanonicalOverBasePoint (ρ ≫ g) (θ : Y) cT
        (crepantPullbackFormUnit ρ hρ c f cT) (q * d)
        (q • cartierPullback ρ D + (d * p) • cartierPullback (ρ ≫ g) H) ↔
          (p : ℚ) / q ≤ (a : ℚ) / q₀) := by
  have hkltT := logPairIsKlt_crepant_pullback_without_properness ρ hρ c f d hd D hklt cT
  obtain ⟨a, q₀, ha, hq₀, -, -, -, U, hUi, hUo, hUN, hUs, σ, hσdom, hσover, hσprop,
      hσ, cU, t, hguard, hpos, hratio, hendpoint, htest⟩ :=
    exists_exact_rational_klt_threshold_over_base_prime_of_klt (ρ ≫ g) θ cT
      (crepantPullbackFormUnit ρ hρ c f cT) d hd (cartierPullback ρ D) hkltT H hH hθ
  exact ⟨a, q₀, ha, hq₀, htest⟩

end MixedFujita
