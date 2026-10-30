/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RealizedProfiles

/-!
For a fixed prime divisor on a smooth birational test model, every real section-value threshold
is exactly a linear subspace condition: use the natural ceiling of the threshold. The zero
section is included via infinite order, and equality of thresholds is retained. Fixed-prime
realization records the centre and positive discrepancy conditions explicitly.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
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

section Order

variable {K : Type u} [Field K] {Y U : Scheme.{u}} [IsIntegral Y] [IsIntegral U]
  [Y.Over (Spec (CommRingCat.of K))] [U.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian U] (σ : U ⟶ Y) [IsDominant σ]
  [σ.IsOver (Spec (CommRingCat.of K))]

/-- A weak real threshold on a prime-divisor value is exactly the corresponding ceiling order
subspace, with the zero section satisfying every threshold. -/
theorem mem_cartierOrderSubspace_ceil_iff (D : CartierDivisor Y) (e : CodimensionOnePoint U)
    [IsDiscreteValuationRing (U.presheaf.stalk (e : U))] (s : Γ(D.sheaf, ⊤)) (t : ℝ) :
    s ∈ cartierStalkPullbackOrderAtLeast (K := K) σ D (e : U) ⌈t⌉₊ ↔
      ∀ hs : s ≠ 0, t ≤ (cartierCoefficient
        (cartierPullback σ (cartierSectionZeroDivisor D s hs)) (e : U) : ℝ) := by
  by_cases hs : s = 0
  · subst s
    constructor
    · intro _ h0
      exact False.elim (h0 rfl)
    · intro _
      exact Submodule.zero_mem _
  · obtain ⟨k, hk, hcoef⟩ :=
      cartierPullback_sectionZeroDivisor_coefficient_eq_stalkPullbackOrder σ D s hs e
    change (⌈t⌉₊ : ℕ∞) ≤ cartierStalkPullbackOrder D σ (e : U) s ↔ _
    rw [hk]
    constructor
    · intro h hs'
      rw [hcoef]
      have hnat : ⌈t⌉₊ ≤ k := by exact_mod_cast h
      have ht : t ≤ (k : ℝ) := Nat.ceil_le.mp hnat
      exact_mod_cast ht
    · intro h
      have ht := h hs
      rw [hcoef] at ht
      have hnat : ⌈t⌉₊ ≤ k := Nat.ceil_le.mpr (by exact_mod_cast ht)
      exact_mod_cast hnat

end Order

section Test

variable {K : Type u} [Field K] {n : ℕ} {Y U : Scheme.{u}} [IsIntegral Y] [IsIntegral U]
  [Y.Over (Spec (CommRingCat.of K))] [U.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian U] [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- Realization by one specified prime divisor, as opposed to existential realization over
all smooth birational test models and prime divisors. -/
def PrimeTestRealizesProfile (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (cU : EtaleChart K U n) (e : CodimensionOnePoint U)
    (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (α : Fin N → ℝ) : Prop :=
  x ∈ closure ({σ (e : U)} : Set Y) ∧
  0 < ((d : ℝ) + cartierCoefficient
    (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d ∧
  ∀ i (hs : s i ≠ 0), α i * (((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) ≤
    (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) hs)) (e : U) : ℝ)

/-- The fixed prime conditions are precisely one subspace membership condition per section,
together with the centre and positive discrepancy conditions independent of the coefficients. -/
theorem primeTestRealizesProfile_iff_orderSubspaces (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (cU : EtaleChart K U n)
    (e : CodimensionOnePoint U) (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    (α : Fin N → ℝ) :
    PrimeTestRealizesProfile σ hσ cY fY d D₀ D cU e x s α ↔
      x ∈ closure ({σ (e : U)} : Set Y) ∧
      0 < ((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d ∧
      ∀ i, s i ∈ cartierStalkPullbackOrderAtLeast (K := K) σ D (e : U)
        ⌈α i * (((d : ℝ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d)⌉₊ := by
  have hsm : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hdvr := smoothOverField_codimensionOne_stalk_DVR (K := K) e
  simp only [PrimeTestRealizesProfile, mem_cartierOrderSubspace_ceil_iff]

/-- A witness from the specified prime is an actual witness in the original existential
realization definition. No completeness of any chosen list of tests is asserted. -/
theorem isRealizedProfile_of_primeTest (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor Y) (cU : EtaleChart K U n) (e : CodimensionOnePoint U)
    (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (α : Fin N → ℝ)
    (h : PrimeTestRealizesProfile σ hσ cY fY d D₀ D cU e x s α) :
    IsRealizedProfile cY fY d D₀ D x s α :=
  ⟨U, inferInstance, inferInstance, inferInstance, inferInstance, σ, inferInstance,
    inferInstance, hσ, cU, e, h⟩

end Test

end MixedFujita
