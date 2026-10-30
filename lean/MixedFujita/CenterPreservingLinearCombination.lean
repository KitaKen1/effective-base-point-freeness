/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NaturalPullbackScalarLinearity
public import MixedFujita.CenterPreservingBertiniParameters

/-! 同じ実有限線形結合の自然制限と元非零性。 See reports/check-262-concentration-residual-snc.json for the verified scope. Actual natural global pullback is semilinear and linear over the actual base ring. SAME finite linear combinations preserve natural restriction, original nonvanishing and exact restricted concentration order. Actual fixed-part removal retains the rational function and recovers the original section. Given actual dominant principalization, the SAME original finite subsystem yields a residual basepointfree family; its linear combinations recover the original combinations with SAME coefficients. Existing global residual Bertini chooses first coefficient nonzero and an actual smooth reduced SNC cut with indicator coefficients. New model construction, final center-exterior LC coefficient bounds, ambient nonLC from restricted concentration, general KV, original L nonvanishing, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable


/-- A finite actual linear combination of the fixed first section and an
ideal-zero family restricts NATURALLY to exactly the first coefficient times
the fixed restricted section. The coefficients are in the actual base ring. -/
theorem fixed_first_linear_combination_natural_restriction
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of R))] (M : X.Modules)
    (k : ℕ) (s₀ : Γ(M, ⊤)) (s : Fin k → Γ(M, ⊤))
    (hzero : ∀ i, modulePullbackGlobalSections φ M (s i) = 0) (a : Fin (k + 1) → R) :
    modulePullbackGlobalSections φ M (∑ i, a i • (Fin.cons s₀ s : Fin (k + 1) → Γ(M, ⊤)) i) =
      a 0 • modulePullbackGlobalSections φ M s₀ := by
  rw [map_sum]
  simp_rw [modulePullbackGlobalSections_smul_base]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, hzero, smul_zero, Finset.sum_const_zero, add_zero]


/-- A nonzero first coefficient and nonzero fixed NATURAL restriction guarantee
BOTH a nonzero restricted linear combination and a nonzero original ambient
section. No original L section or center normality is assumed. -/
theorem fixed_first_linear_combination_natural_and_ambient_ne_zero
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (φ : Y ⟶ X) [φ.IsOver (Spec (CommRingCat.of K))] (M : X.Modules)
    (k : ℕ) (s₀ : Γ(M, ⊤)) (h₀ : modulePullbackGlobalSections φ M s₀ ≠ 0)
    (s : Fin k → Γ(M, ⊤)) (hzero : ∀ i, modulePullbackGlobalSections φ M (s i) = 0)
    (a : Fin (k + 1) → K) (ha : a 0 ≠ 0) :
    modulePullbackGlobalSections φ M (∑ i, a i • (Fin.cons s₀ s : Fin (k + 1) → Γ(M, ⊤)) i) ≠ 0 ∧
      (∑ i, a i • (Fin.cons s₀ s : Fin (k + 1) → Γ(M, ⊤)) i) ≠ 0 := by
  have hres : modulePullbackGlobalSections φ M
      (∑ i, a i • (Fin.cons s₀ s : Fin (k + 1) → Γ(M, ⊤)) i) ≠ 0 := by
    rw [fixed_first_linear_combination_natural_restriction φ M k s₀ s hzero a]
    exact smul_ne_zero ha h₀
  refine ⟨hres, fun hz => hres ?_⟩
  rw [hz, map_zero]

end MixedFujita
