/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperInfinitesimalVanishing

/-! Actual kernels of successive infinitesimal quotient maps and propagation
of cohomology vanishing. The quotient with index `n` is modulo `I^(n+1)`.
No identification of a kernel with a proposed geometric model is assumed here. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits Abelian
namespace MixedFujita
open TauCeti.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The actual successive layer from `M / I^(n+2) M` to `M / I^(n+1) M`. -/
noncomputable def infinitesimalCohomologyLayer {A : CommRingCat.{u}}
    {T : Scheme.{u}} (f : T ⟶ Spec A) (I : Ideal A) (M : T.Modules) (n : ℕ) :
    T.Modules := kernel (M.quotientIdealPowMap f I n)

theorem quotientIdealPowMap_epi {A : CommRingCat.{u}} {T : Scheme.{u}}
    (f : T ⟶ Spec A) (I : Ideal A) (M : T.Modules) (n : ℕ) :
    Epi (M.quotientIdealPowMap f I n) :=
  epi_of_epi_fac (M.toQuotientIdealPow_comp_map f I n)

/-- Short exactness is proved for the actual transition map. -/
theorem infinitesimalCohomologyLayer_shortExact {A : CommRingCat.{u}}
    {T : Scheme.{u}} (f : T ⟶ Spec A) (I : Ideal A) (M : T.Modules) (n : ℕ) :
    (ShortComplex.mk (kernel.ι (M.quotientIdealPowMap f I n))
      (M.quotientIdealPowMap f I n) (kernel.condition _)).ShortExact := by
  let := quotientIdealPowMap_epi f I M n
  exact { exact := ShortComplex.exact_kernel _ }

/-- Same-degree vanishing on both ends of an actual short exact sequence
forces vanishing in the middle. -/
theorem actual_cohomology_vanish_of_shortExact {T : Scheme.{u}}
    (S : ShortComplex T.Modules) (hS : S.ShortExact) (q : ℕ)
    (h₁ : Subsingleton (Scheme.Modules.Cohomology S.X₁ q))
    (h₃ : Subsingleton (Scheme.Modules.Cohomology S.X₃ q)) :
    Subsingleton (Scheme.Modules.Cohomology S.X₂ q) := by
  let := h₁
  let := h₃
  let : Subsingleton (S.X₁.H q) := (sgaCohomologyLinearEquiv _ q).subsingleton
  let : Subsingleton (S.X₃.H q) := (sgaCohomologyLinearEquiv _ q).subsingleton
  let : Subsingleton (S.X₂.H q) := subsingleton_of_forall_eq 0 fun x => by
    obtain ⟨y, hy⟩ := (AlgebraicGeometry.Scheme.Modules.H'.exact_map_map hS q ⊤ x).mp
      (Subsingleton.elim _ _)
    rw [← hy, Subsingleton.elim y 0]
    exact map_zero _
  exact (sgaCohomologyLinearEquiv S.X₂ q).symm.subsingleton

theorem quotient_cohomology_vanish_succ {A : CommRingCat.{u}} {T : Scheme.{u}}
    (f : T ⟶ Spec A) (I : Ideal A) (M : T.Modules) (q n : ℕ)
    (hQ : Subsingleton (Scheme.Modules.Cohomology (M.quotientIdealPow f I n) q))
    (hL : Subsingleton (Scheme.Modules.Cohomology
      (infinitesimalCohomologyLayer f I M n) q)) :
    Subsingleton (Scheme.Modules.Cohomology (M.quotientIdealPow f I (n + 1)) q) :=
  actual_cohomology_vanish_of_shortExact _
    (infinitesimalCohomologyLayer_shortExact f I M n) q hL hQ

/-- Starting at any level, vanishing of its later layers propagates upward. -/
theorem quotient_cohomology_vanish_from_layers {A : CommRingCat.{u}}
    {T : Scheme.{u}} (f : T ⟶ Spec A) (I : Ideal A) (M : T.Modules) (q N : ℕ)
    (hQ : Subsingleton (Scheme.Modules.Cohomology (M.quotientIdealPow f I N) q))
    (hL : ∀ n ≥ N, Subsingleton (Scheme.Modules.Cohomology
      (infinitesimalCohomologyLayer f I M n) q)) :
    ∀ n ≥ N, Subsingleton (Scheme.Modules.Cohomology (M.quotientIdealPow f I n) q) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hQ
  | succ n hn ih => exact quotient_cohomology_vanish_succ f I M q n ih (hL n hn)

/-- A tail of actual layers and one initial quotient suffice over any proper
Noetherian base with an ideal contained in the Jacobson radical. -/
theorem proper_cohomology_vanish_from_layers {A : CommRingCat.{u}}
    [IsNoetherianRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    {T : Scheme.{u}} (f : T ⟶ Spec A) [IsProper f] (M : T.Modules) [M.IsCoherent]
    (q N : ℕ)
    (hQ : Subsingleton (Scheme.Modules.Cohomology (M.quotientIdealPow f I N) q))
    (hL : ∀ n ≥ N, Subsingleton (Scheme.Modules.Cohomology
      (infinitesimalCohomologyLayer f I M n) q)) :
    Subsingleton (Scheme.Modules.Cohomology M q) := by
  apply proper_cohomology_vanish_of_cofinal_quotients I hI f M q
  intro c
  exact ⟨max c N, le_max_left _ _,
    quotient_cohomology_vanish_from_layers f I M q N hQ hL _ (le_max_right _ _)⟩

end MixedFujita
