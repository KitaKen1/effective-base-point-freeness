/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefPulledMixedEuler
public import MixedFujita.CoherentMixedEulerPositivityReduction
public import MixedFujita.AmpleCartierPullbackRepresentatives

/-! 任意nef族の非被約proper閉源・実連接係数への拡張。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Arbitrary original nef families have nonnegative actual coherent top
coefficients on possibly nonreduced proper closed sources. -/
theorem proper_closed_pulled_nef_coherentMixedEuler_nonneg
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) [IsClosedImmersion p] [p.IsOver (Spec (CommRingCat.of K))]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    (D : List (CartierDivisor X)) (hlen : D.length = n + 1)
    (hD : ∀ F ∈ D, CartierIsNef K F) (M : Y.Modules) [M.IsCoherent] (E : CartierDivisor X) :
    0 ≤ cartierPulledModuleMixedEulerDifference K p M D E := by
  apply proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_integral_units
    K n hdim p D (by omega) E ?_ M
  intro Z _ _ _ i _ _
  let t := i ≫ p
  obtain ⟨AZ, ⟨aA⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor A t
  have hAZ := cartierHasHyperplanePower_of_closed_representative K t A AZ aA
    (cartierHasHyperplanePower_of_isAmpleProj K A hA)
  exact proper_pulled_nef_unit_top_nonneg K n
    (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
    (cartierHasHyperplanePower_exists_ample K AZ hAZ) t D hlen hD E

end MixedFujita
