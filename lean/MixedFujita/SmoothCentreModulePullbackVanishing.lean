/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothCentreAllPointVanishing
public import MixedFujita.SignedEffectiveCartierPullback
public import MixedFujita.ActualCartierSerreVanishing

/-! Positive cohomology of the ordinary module pullback vanishes on every
actual stalk blow-up for a signed effective source combination with bounded
exceptional correction. The Cartier/module comparison is constructed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 1000000 in
theorem smoothCentre_allPoint_modulePullback_vanish
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) (n r : ℕ) [SmoothOfRelativeDimension n f]
    (Z : X.IdealSheafData) [SmoothOfRelativeDimension (n - (r + 1)) (Z.subschemeι ≫ f)]
    [IsIntegral Z.blowUp] [IsDominant Z.blowUpπ]
    (hrn : r + 1 ≤ n) (E : CartierDivisor Z.blowUp) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = Z.exceptionalDivisor)
    {ι : Type*} [Fintype ι] (P : ι → CartierDivisor X) (hP : ∀ i, (P i).IsEffective)
    (a : ι → ℤ) (C : CartierDivisor Z.blowUp) (j : ℕ) (hj : j ≤ r)
    (hC : C = cartierPullback Z.blowUpπ (∑ i, a i • P i) + j • E) (x : X) :
    let := affineBlowUp_isIntegral_of_ne_bot (Z.stalkIdeal x)
      (smoothCentre_stalkIdeal_ne_bot f n r Z hrn x)
    ∃ (τ : affineBlowUp (Z.stalkIdeal x) ⟶ Z.blowUp) (hτ : IsDominant τ),
      let := hτ
      IsPullback τ (affineBlowUp.π (Z.stalkIdeal x)) Z.blowUpπ (X.fromSpecStalk x) ∧
      Nonempty ((Scheme.Modules.pullback τ).obj C.sheaf ≅ (cartierPullback τ C).sheaf) ∧
      ∀ q : ℕ, Subsingleton
        (Scheme.Modules.Cohomology ((Scheme.Modules.pullback τ).obj C.sheaf) (q + 1)) := by
  let := affineBlowUp_isIntegral_of_ne_bot (Z.stalkIdeal x)
    (smoothCentre_stalkIdeal_ne_bot f n r Z hrn x)
  obtain ⟨τ, hτ, H, hv⟩ := smoothCentre_allPoint_local_exceptional_combination_vanish
    f n r Z hrn E hE hEI _ C j hj hC x
  let := hτ
  obtain ⟨e⟩ := signed_exceptional_combination_pullback_moduleIso
    Z.blowUpπ τ P hP a E hE j C hC
  refine ⟨τ, hτ, H, ⟨e⟩, fun q ↦ ?_⟩
  let := hv q
  exact (actualCohomologyLinearEquivOfIso e (q + 1)).subsingleton

end MixedFujita
