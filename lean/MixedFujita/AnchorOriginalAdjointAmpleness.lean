/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ConcentrationLCAmpleAdjoint

/-! 固定klt基準対・摂動を吸収する元L随伴の全大混合ample性。 See reports/check-267-klt-anchor-center-isolation.json for the verified scope. A fixed rational perturbation ratio and all-large mixing with an actual klt anchor retain only OLD positive-perturbation critical components and preserve ORIGINAL L ample adjoints. On a SUPPLIED actual shared proper SNC model with a SUPPLIED actual effective source perturbation and critical-placement/positivity inputs, the entire ORIGINAL nonKlt locus equals the chosen minimal lc center. The exact reduced center ideal is internally identified, and EXPLICIT usual H1 KV yields original Cartier and all-large ORIGINAL mL restriction lifting. Constructing the isolation perturbation/model/placement/positivity and numerical-zero center nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- A fixed rational perturbation and klt anchor preserve an ample ORIGINAL
L-adjoint for EVERY sufficiently large mixing coefficient N. No ampleness
of the anchor's adjoint and no canonical Cartier divisor are assumed. -/
theorem lc_anchor_perturbed_original_adjoint_eventually_ample
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (L D A M : CartierDivisor X) (d b p q : ℕ) (hq : 1 ≤ q)
    (hH : CartierIsAmpleProj K ((d * b) • L - D)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      CartierIsAmpleProj K (((q * (N + 1) * d) * b) • L - (q • (N • D + A) + p • M)) := by
  let H := (d * b) • L - D
  let F := q • ((d * b) • L - A) - p • M
  have hqH := cartierIsAmpleProj_nsmul hH hq
  obtain ⟨N₀, hN₀⟩ := cartierIsAmpleProj_eventually_twist_veryAmple hqH F
  refine ⟨N₀, fun N hN => ?_⟩
  have h := cartierIsAmpleProj_of_veryAmple (hN₀ N hN)
  have heq : F + N • (q • H) =
      (((q * (N + 1) * d) * b) • L - (q • (N • D + A) + p • M)) := by
    dsimp only [F, H]
    module
  exact heq ▸ h

end MixedFujita
