/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EtaleChartDimension
public import MixedFujita.FiniteTypeClosedPointEvaluation
public import MixedFujita.TaylorFiniteJets
public import MixedFujita.CartierVanishingOrder

/-! 特異源の実étale閉点Taylorと有限箱高次数切断。 See reports/check-253-singular-concentration-nonLC-point.json for the verified scope. Actual etale chart completions evaluate original global Cartier sections on a possibly singular integral source, without global smoothness. Original normal klt BPF data with positive numerical dimension construct all-high-power concentrated effective divisors at smooth closed points, without an initial L section or KV. Actual high regular-equation order obstructs the original all-model pointwise log-canonical and klt predicates. A boundary-free closed point in any nonempty open and effective non-lc perturbations are constructed internally. Initial and restricted nonvanishing, lc-threshold ample preservation, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower


/-- Actual Cartier sections on a possibly singular integral finite-type source
have an injective order-preserving Taylor map at every closed point of an
actual etale chart. No global smoothness or supplied completion is needed. -/
theorem etaleChart_closedPoint_exists_actualCartierTaylorData
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}
    (c : EtaleChart K X n) (D : CartierDivisor X) (x : X) (hx : x ∈ c.U)
    (hclosed : IsClosed {x}) :
    ∃ (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f),
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
        ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
          cartierSectionVanishingOrder D x s := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  obtain ⟨β⟩ := finiteTypeScheme_closedPoint_has_localEvaluation (K := K) x hclosed
  obtain ⟨e, _, _⟩ := etaleChart_exists_taylorCoordinates c x hx β
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  exact ⟨f, hf, e, cartierTaylorCoordinates_injective D x f hf e,
    cartierTaylorCoordinates_order_eq_vanishingOrder D x f hf e⟩


/-- Finite Taylor boxes on an actual etale chart force high intrinsic order
of an actual nonzero original global section, without global smoothness. -/
theorem etaleChart_closedPoint_exists_high_order_section_of_finrank_gt_box
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}
    (c : EtaleChart K X n) (D : CartierDivisor X) (x : X) (hx : x ∈ c.U)
    (hclosed : IsClosed {x}) (d : ℕ)
    (hlarge : (d + 1) ^ n < Module.finrank K Γ(D.sheaf, ⊤)) :
    ∃ s : Γ(D.sheaf, ⊤), s ≠ 0 ∧ (d : ℕ∞) < cartierSectionVanishingOrder D x s := by
  obtain ⟨f, hf, e, _, hord⟩ := etaleChart_closedPoint_exists_actualCartierTaylorData c D x hx hclosed
  by_contra h
  have hbound : ∀ s : Γ(D.sheaf, ⊤), s ≠ 0 → (cartierTaylorCoordinates D x f hf e s).order ≤ d := by
    intro s hs
    rw [hord s]
    exact le_of_not_gt (fun hgt => h ⟨s, hs, hgt⟩)
  exact (not_le_of_gt hlarge) (finrank_le_box_of_linearTaylor_order_bound n d _ hbound)


/-- At every smooth closed point of a possibly singular integral variety,
the dimension criterion yields an actual high-order global section. -/
theorem smoothLocus_closedPoint_exists_high_order_section_of_finrank_gt_box
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D : CartierDivisor X)
    (x : X) (hx : x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus)
    (hclosed : IsClosed {x}) (d : ℕ)
    (hlarge : (d + 1) ^ n < Module.finrank K Γ(D.sheaf, ⊤)) :
    ∃ s : Γ(D.sheaf, ⊤), s ≠ 0 ∧ (d : ℕ∞) < cartierSectionVanishingOrder D x s := by
  obtain ⟨m, c, hc⟩ := exists_etaleChart_of_mem_smoothLocus (K := K) hx
  have hmn : m = n := by exact_mod_cast (etaleChart_topologicalKrullDim c).symm.trans hdim
  subst m
  exact etaleChart_closedPoint_exists_high_order_section_of_finrank_gt_box c D x hc hclosed d hlarge

end MixedFujita
