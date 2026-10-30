/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CrepantBoundaryPerturbation
public import MixedFujita.LogPairDenominatorScaling

/-! 実対の自然数線形結合のcrepant境界とeffectivity。 See reports/check-267-klt-anchor-center-isolation.json for the verified scope. A fixed rational perturbation ratio and all-large mixing with an actual klt anchor retain only OLD positive-perturbation critical components and preserve ORIGINAL L ample adjoints. On a SUPPLIED actual shared proper SNC model with a SUPPLIED actual effective source perturbation and critical-placement/positivity inputs, the entire ORIGINAL nonKlt locus equals the chosen minimal lc center. The exact reduced center ideal is internally identified, and EXPLICIT usual H1 KV yields original Cartier and all-large ORIGINAL mL restriction lifting. Constructing the isolation perturbation/model/placement/positivity and numerical-zero center nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Crepant boundaries are affine in ACTUAL pair presentations, including
mixing distinct lc/klt pairs without assuming the canonical class Cartier. -/
theorem crepantBoundaryCartier_natural_combination
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d e a b : ℕ)
    (D E : CartierDivisor X) (cT : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    crepantBoundaryCartier ρ hρ c f (a * d + b * e) (a • D + b • E) cT hT =
      a • crepantBoundaryCartier ρ hρ c f d D cT hT +
        b • crepantBoundaryCartier ρ hρ c f e E cT hT := by
  unfold crepantBoundaryCartier
  rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_nsmul]
  module


/-- Nonnegative mixing of two EFFECTIVE actual pair boundaries preserves
boundary effectivity; the presentations may have different denominators. -/
theorem logPairBoundaryEffective_natural_combination
    {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d e a b : ℕ) (D E : CartierDivisor X)
    (hD : LogPairBoundaryEffective c f d D) (hE : LogPairBoundaryEffective c f e E) :
    LogPairBoundaryEffective c f (a * d + b * e) (a • D + b • E) := by
  intro c' x hx hcod
  have hD' := mul_le_mul_of_nonneg_left (hD c' x hx hcod) (by exact_mod_cast Nat.zero_le a : (0 : ℤ) ≤ a)
  have hE' := mul_le_mul_of_nonneg_left (hE c' x hx hcod) (by exact_mod_cast Nat.zero_le b : (0 : ℤ) ≤ b)
  rw [cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_nsmul]
  push_cast at hD' hE' ⊢
  nlinarith

end MixedFujita
