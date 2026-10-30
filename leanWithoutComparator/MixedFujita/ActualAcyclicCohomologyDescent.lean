/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BlowUpSequenceAcyclicPushforward
public import MixedFujita.SGACohomologyComparison

/-!
All-degree descent for actual module cohomology.

The compact-open SGA comparison is transported to the cohomology type used by
Kawamata--Viehweg vanishing. Relative acyclicity is an explicit hypothesis here;
the SNC component-correction theorem supplies it geometrically in applications.
An ordinary direct-image isomorphism alone does not imply this comparison.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual global cohomology in every degree agrees across an acyclic
pushforward. No field, properness, or derived-direct-image dictionary is needed. -/
noncomputable def acyclicPushforwardActualCohomologyAddEquiv
    {T X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (f : T ⟶ X) (M : T.Modules) (N : X.Modules) [N.IsQuasicoherent]
    (e : N ≅ (Scheme.Modules.pushforward f).obj M)
    (hvan : ∀ V : X.Opens, IsAffineOpen V → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) (f ⁻¹ᵁ V))) (j : ℕ) :
    Scheme.Modules.Cohomology M j ≃+ Scheme.Modules.Cohomology N j := by
  have e' := acyclicPushforwardIsoCompactOpenAddEquiv f M N e hvan ⊤ isCompact_univ j
  rw [Scheme.Hom.preimage_top] at e'
  exact (sgaCohomologyLinearEquiv M j).symm.toAddEquiv.trans
    (e'.trans (sgaCohomologyLinearEquiv N j).toAddEquiv)

/-- The actual vanishing comparison works in both directions and in all degrees. -/
theorem actual_cohomology_subsingleton_iff_of_acyclic_pushforward
    {T X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (f : T ⟶ X) (M : T.Modules) (N : X.Modules) [N.IsQuasicoherent]
    (e : N ≅ (Scheme.Modules.pushforward f).obj M)
    (hvan : ∀ V : X.Opens, IsAffineOpen V → ∀ q : ℕ,
      Subsingleton (M.H' (q + 1) (f ⁻¹ᵁ V))) (j : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology M j) ↔
      Subsingleton (Scheme.Modules.Cohomology N j) := by
  let a := acyclicPushforwardActualCohomologyAddEquiv f M N e hvan j
  constructor
  · intro h
    let := h
    exact a.symm.subsingleton
  · intro h
    let := h
    exact a.subsingleton

/-- Compose the existing analytic step data of a blow-up sequence and obtain
the comparison in the actual cohomology type, for every degree including zero. -/
theorem blowUpSequence_actual_cohomology_comparison
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    (S : Scheme.BlowUpSequence X) (M : X.Modules) [M.IsQuasicoherent]
    (N : S.last.Modules) (h : blowUpSequenceAcyclicModules S M N) (j : ℕ) :
    Nonempty (Scheme.Modules.Cohomology N j ≃+ Scheme.Modules.Cohomology M j) := by
  obtain ⟨⟨e⟩, hv, _⟩ := blowUpSequence_acyclic_pushforward S M N h
  exact ⟨acyclicPushforwardActualCohomologyAddEquiv S.composite N M e hv j⟩

/-- Vanishing on the last model descends through a whole sequence once its
stepwise geometric data have supplied `blowUpSequenceAcyclicModules`. -/
theorem blowUpSequence_actual_cohomology_vanishing_descent
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    (S : Scheme.BlowUpSequence X) (M : X.Modules) [M.IsQuasicoherent]
    (N : S.last.Modules) (h : blowUpSequenceAcyclicModules S M N) (j : ℕ)
    (hN : Subsingleton (Scheme.Modules.Cohomology N j)) :
    Subsingleton (Scheme.Modules.Cohomology M j) := by
  obtain ⟨a⟩ := blowUpSequence_actual_cohomology_comparison S M N h j
  let := hN
  exact a.symm.subsingleton

end MixedFujita
