/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleIdealExactBaseLocus

/-! 集中切断付き族の自然制限と先頭非零Bertiniパラメータ。 See reports/check-261-exact-center-base-canonical-pullback.json for the verified scope. Tracking GLOBAL1 proves exact compatibility of canonical section homs and NATURAL global pullback. Mathlib biproduct formulas identify exterior finite-free pullback with canonical generation by the SAME naturally pulled family. Actual stalk maps reflect unit coefficients without target integrality. ALL high original ample powers have an actual ambient finite family naturally zero on the actual closed center with common ZERO SET exactly its support and a unit coefficient at every point off support. Adding the fixed concentrated lift gives restriction vector (fixed,0,...,0) and exact common zero set. Multiplying a nonzero parameter polynomial by X_0 ensures first coefficient nonzero over an infinite field. Actual SNC exterior-LC Bertini geometry, linear-combination scalar/concentration preservation, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

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


/-- Append a fixed concentrated lift as the FIRST member of the actual ideal
family. Its exact common zero locus is the old center intersected with the
fixed cut, and its NATURAL restriction family is exactly (fixed,0,...,0).
This constructs the linear family used by the concentration/Bertini argument. -/
theorem fixed_lift_and_ideal_family_exact_base_and_natural_restrictions
    {X : Scheme.{u}} [IsIntegral X] (P : CartierDivisor X) (I : X.IdealSheafData)
    (k : ℕ) (s : Fin k → Γ(P.sheaf, ⊤))
    (hzero : ∀ i, modulePullbackGlobalSections I.subschemeι P.sheaf (s i) = 0)
    (hbase : ∀ x : X, (∀ i, x ∈ cartierSectionZeroLocus P (s i)) ↔ x ∈ I.support)
    (s₀ : Γ(P.sheaf, ⊤)) :
    (∀ i : Fin (k + 1), modulePullbackGlobalSections I.subschemeι P.sheaf ((Fin.cons s₀ s : Fin (k + 1) → Γ(P.sheaf, ⊤)) i) =
      (Fin.cons (modulePullbackGlobalSections I.subschemeι P.sheaf s₀) (fun _ : Fin k => 0) :
        Fin (k + 1) → Γ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf, ⊤)) i) ∧
    ∀ x : X, (∀ i : Fin (k + 1), x ∈ cartierSectionZeroLocus P ((Fin.cons s₀ s : Fin (k + 1) → Γ(P.sheaf, ⊤)) i)) ↔
      x ∈ I.support ∧ x ∈ cartierSectionZeroLocus P s₀ := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact hzero j
  · intro x
    rw [Fin.forall_fin_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hbase x]
    exact and_comm


/-- A nonempty Bertini parameter open can be intersected with the FIRST
coefficient being nonzero over an infinite field. Multiplying its polynomial
by X_0 avoids an extra geometric finite-point-avoidance construction. -/
theorem exists_polynomial_good_parameter_with_first_coefficient_ne_zero
    {K : Type u} [Field K] [Infinite K] (k : ℕ)
    (p : MvPolynomial (Fin (k + 1)) K) (hp : p ≠ 0) :
    ∃ t : Fin (k + 1) → K, MvPolynomial.aeval t p ≠ 0 ∧ t 0 ≠ 0 := by
  classical
  have hprod : p * MvPolynomial.X (0 : Fin (k + 1)) ≠ 0 := mul_ne_zero hp (MvPolynomial.X_ne_zero _)
  have hex : ∃ t : Fin (k + 1) → K,
      MvPolynomial.aeval t (p * MvPolynomial.X (0 : Fin (k + 1))) ≠ 0 := by
    by_contra h
    push Not at h
    apply hprod
    apply MvPolynomial.funext
    intro t
    rw [map_zero]
    exact h t
  obtain ⟨t, ht⟩ := hex
  rw [map_mul, MvPolynomial.aeval_X] at ht
  exact ⟨t, (mul_ne_zero_iff.mp ht).1, (mul_ne_zero_iff.mp ht).2⟩

end MixedFujita
