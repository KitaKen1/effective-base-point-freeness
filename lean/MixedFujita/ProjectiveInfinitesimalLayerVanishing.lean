/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalCohomologyLayers
public import MixedFujita.ActualCartierSerreVanishing
public import SGA.Foundations.Cohomology.ProjectiveSpaceTwist

/-! Explicit projective-space calculations, including negative twists, supply
vanishing for actual infinitesimal layers with the stated sheaf isomorphisms.
The geometric identifications are inputs; this does not construct them for an
arbitrary birational SNC model. The pinned SGA calculation is used directly. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
open TauCeti.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The exact degree bound for actual positive cohomology of `O(d)`. -/
theorem actual_projectiveSpace_twist_vanish (B : Type u) [CommRing B]
    (r q : ℕ) (d : ℤ) (h : q + 1 ≠ r ∨ -((r : ℤ) + 1) < d) :
    Subsingleton (Scheme.Modules.Cohomology
      (projectiveSpace.twist (Fin (r + 1)) B d) (q + 1)) := by
  let := projectiveSpace.H_twist_subsingleton B r q d h
  exact (sgaCohomologyLinearEquiv _ (q + 1)).symm.subsingleton

/-- In degree different from the projective dimension every twist works.
In the top degree, `k ≤ r` makes every `O(n-k)`, `n ≥ 0`, acyclic. -/
theorem actual_projectiveSpace_shifted_twist_vanish (B : Type u) [CommRing B]
    (r q k n : ℕ) (h : q + 1 ≠ r ∨ k ≤ r) :
    Subsingleton (Scheme.Modules.Cohomology
      (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) - k)) (q + 1)) := by
  apply actual_projectiveSpace_twist_vanish
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- Explicit projective models of the first quotient and actual later kernels
give whole-source vanishing. In particular, for H1 and `r ≠ 1` no twist bound
is needed. The base need not be complete. -/
theorem proper_cohomology_vanish_of_projective_layers
    {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson ⊥) {T : Scheme.{u}} (f : T ⟶ Spec A) [IsProper f]
    (M : T.Modules) [M.IsCoherent] (B : Type u) [CommRing B] (r q k : ℕ)
    (e : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) B) ⟶ T)
    [IsClosedImmersion e]
    (a₀ : M.quotientIdealPow f I 0 ≅ (Scheme.Modules.pushforward e).obj
      (projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ))))
    (aL : ∀ n : ℕ, infinitesimalCohomologyLayer f I M n ≅
      (Scheme.Modules.pushforward e).obj
        (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) + 1 - k)))
    (h : q + 1 ≠ r ∨ k ≤ r) :
    Subsingleton (Scheme.Modules.Cohomology M (q + 1)) := by
  have hv (n : ℕ) : Subsingleton (Scheme.Modules.Cohomology
      ((Scheme.Modules.pushforward e).obj
        (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) - k))) (q + 1)) := by
    let := actual_projectiveSpace_shifted_twist_vanish B r q k n h
    exact (closedImmersionCohomologyAddEquiv e _ (q + 1)).subsingleton
  apply proper_cohomology_vanish_from_layers I hI f M (q + 1) 0
  · let : Subsingleton (Scheme.Modules.Cohomology
        ((Scheme.Modules.pushforward e).obj
          (projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ)))) (q + 1)) := by
      simpa only [Nat.cast_zero, zero_sub] using hv 0
    exact (actualCohomologyLinearEquivOfIso a₀ (q + 1)).subsingleton
  · intro n _
    let : Subsingleton (Scheme.Modules.Cohomology
        ((Scheme.Modules.pushforward e).obj
          (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) + 1 - k))) (q + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hv (n + 1)
    exact (actualCohomologyLinearEquivOfIso (aL n) (q + 1)).subsingleton

/-- The maximal-ideal specialization needed over local bases. No separate
Jacobson-radical certificate or completeness assumption is supplied. -/
theorem proper_local_cohomology_vanish_of_projective_layers
    {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
    {T : Scheme.{u}} (f : T ⟶ Spec A) [IsProper f]
    (M : T.Modules) [M.IsCoherent] (B : Type u) [CommRing B] (r q k : ℕ)
    (e : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) B) ⟶ T)
    [IsClosedImmersion e]
    (a₀ : M.quotientIdealPow f (IsLocalRing.maximalIdeal A) 0 ≅
      (Scheme.Modules.pushforward e).obj
        (projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ))))
    (aL : ∀ n : ℕ, infinitesimalCohomologyLayer f (IsLocalRing.maximalIdeal A) M n ≅
      (Scheme.Modules.pushforward e).obj
        (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) + 1 - k)))
    (h : q + 1 ≠ r ∨ k ≤ r) :
    Subsingleton (Scheme.Modules.Cohomology M (q + 1)) :=
  proper_cohomology_vanish_of_projective_layers _
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A)) f M B r q k e a₀ aL h

end MixedFujita
