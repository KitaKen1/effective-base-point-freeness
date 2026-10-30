/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenters
public import MixedFujita.LogCanonicalDenominatorScaling

/-! 実lc中心の正整数分母倍での不変性。 See reports/check-268-internal-lc-center-isolation.json for the verified scope. ACTUAL minimal-lc-center isolation now internally constructs the original center ideal finite system, SAME-original-family principalization/residual Bertini, source perturbation, shared SNC model, old-critical positivity and placement. A contained lc center obstructs every positive perturbation, forcing a positive old-critical coefficient on ANY joint model by finite-LC-threshold contradiction. Arbitrary anchor denominators are normalized retaining actual centers. Original positive-numerical klt BPF assumptions construct an isolated restricted-numerical-zero center; EXPLICIT usual H1 KV gives exact-center original mL lifting. Zero-dimensional minimal centers yield original nonvanishing under usual KV. Positive-dimensional numerical-zero-center nonvanishing, general KV, the original nu=0 branch, unconditional BPF and full F1/F2 remain unproved. -/

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


/-- Genuine valuative lc centers are unchanged by positive denominator
scaling, retaining their ACTUAL discrepancy-prime witness and closed set. -/
theorem logPairIsLogCanonicalCenter_scale_denominator_iff
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d m : ℕ) (hm : 1 ≤ m)
    (D : CartierDivisor X) (Z : Closeds X) :
    LogPairIsLogCanonicalCenter c f (m * d) (m • D) Z ↔ LogPairIsLogCanonicalCenter c f d D Z := by
  constructor
  · rintro ⟨hlc, T, hTi, hTN, hTo, hTs, ρ, hdom, hover, hproper, hρ, cT, t, ht, hdisc, hset⟩
    let := hTi
    let := hTN
    let := hTo
    let := hTs
    let := hdom
    let := hover
    let := hproper
    refine ⟨(logPairIsLogCanonical_scale_denominator_iff c f d m hm D).mp hlc,
      T, hTi, hTN, hTo, hTs, ρ, hdom, hover, hproper, hρ, cT, t, ht, ?_, hset⟩
    rw [logDiscrepancyDivisor_scale_denominator, cartierCoefficient_nsmul] at hdisc
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
    push_cast at hdisc
    nlinarith
  · rintro ⟨hlc, T, hTi, hTN, hTo, hTs, ρ, hdom, hover, hproper, hρ, cT, t, ht, hdisc, hset⟩
    let := hTi
    let := hTN
    let := hTo
    let := hTs
    let := hdom
    let := hover
    let := hproper
    refine ⟨(logPairIsLogCanonical_scale_denominator_iff c f d m hm D).mpr hlc,
      T, hTi, hTN, hTo, hTs, ρ, hdom, hover, hproper, hρ, cT, t, ht, ?_, hset⟩
    rw [logDiscrepancyDivisor_scale_denominator, cartierCoefficient_nsmul, hdisc]
    push_cast
    ring

end MixedFujita
