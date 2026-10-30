/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACohomologyComparison
public import SGA.Foundations.Cohomology.FormalFunctions
public import Mathlib.RingTheory.Nakayama

/-! Artin--Rees and Nakayama give a finite-thickness criterion for actual
proper coherent cohomology. Completeness of the base is not required.
The ideal must lie in the Jacobson radical. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- For one internally obtained Artin--Rees threshold, vanishing on any
sufficiently thick infinitesimal neighborhood forces actual global vanishing. -/
theorem proper_cohomology_vanish_of_sufficiently_thick_quotient
    {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson ⊥) {T : Scheme.{u}} (f : T ⟶ Spec A) [IsProper f]
    (M : T.Modules) [M.IsCoherent] (q : ℕ) :
    ∃ c : ℕ, ∀ n ≥ c,
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (M.quotientIdealPow f I n) q) →
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M q) := by
  let := M.moduleOver f q ⊤
  let : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : Module.Finite A (M.H q) := properFinitenessStatement A T f M q
  obtain ⟨c, hc⟩ := exists_range_ιPow_le I f M q
  refine ⟨c, fun n hn hvan => ?_⟩
  let := hvan
  let : Subsingleton ((M.quotientIdealPow f I n).H q) :=
    (sgaCohomologyLinearEquiv _ q).subsingleton
  have htop : (⊤ : Submodule A (M.H q)) ≤ I • ⊤ := by
    intro x _
    obtain ⟨y, hy⟩ := (Scheme.Modules.H'.exact_map_map
      (shortExact_quotientIdealPow f I M n) q ⊤ x).mp (Subsingleton.elim _ _)
    have hmem := hc (n + 1) 1 (by omega) y
    simpa only [pow_one, hy] using hmem
  have he := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I
    (⊤ : Submodule A (M.H q)) Module.Finite.fg_top htop hI
  let : Subsingleton (M.H q) := subsingleton_of_forall_eq 0 fun x => by
    have hx : x ∈ (⊤ : Submodule A (M.H q)) := trivial
    rwa [he, Submodule.mem_bot] at hx
  exact (sgaCohomologyLinearEquiv M q).symm.subsingleton

/-- Vanishing on a cofinal set of thickenings suffices; no inverse limit
or complete local base is added as an assumption. -/
theorem proper_cohomology_vanish_of_cofinal_quotients
    {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson ⊥) {T : Scheme.{u}} (f : T ⟶ Spec A) [IsProper f]
    (M : T.Modules) [M.IsCoherent] (q : ℕ)
    (hvan : ∀ c : ℕ, ∃ n ≥ c,
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (M.quotientIdealPow f I n) q)) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M q) := by
  obtain ⟨c, hc⟩ := proper_cohomology_vanish_of_sufficiently_thick_quotient I hI f M q
  obtain ⟨n, hn, hv⟩ := hvan c
  exact hc n hn hv

/-- In particular, vanishing at every infinitesimal level gives vanishing
of the actual proper coherent cohomology group. -/
theorem proper_cohomology_vanish_of_all_quotients
    {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A)
    (hI : I ≤ Ideal.jacobson ⊥) {T : Scheme.{u}} (f : T ⟶ Spec A) [IsProper f]
    (M : T.Modules) [M.IsCoherent] (q : ℕ)
    (hvan : ∀ n : ℕ,
      Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (M.quotientIdealPow f I n) q)) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology M q) :=
  proper_cohomology_vanish_of_cofinal_quotients I hI f M q (fun c => ⟨c, le_rfl, hvan c⟩)

end MixedFujita
