/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SmoothLocusAmpleConcentration
public import MixedFujita.PositiveNumericalPencilVolume

/-! 正の元数値次元から特異源smooth点の明示pencil集中。 See reports/check-253-singular-concentration-nonLC-point.json for the verified scope. Actual etale chart completions evaluate original global Cartier sections on a possibly singular integral source, without global smoothness. Original normal klt BPF data with positive numerical dimension construct all-high-power concentrated effective divisors at smooth closed points, without an initial L section or KV. Actual high regular-equation order obstructs the original all-model pointwise log-canonical and klt predicates. A boundary-free closed point in any nonempty open and effective non-lc perturbations are constructed internally. Initial and restricted nonvanishing, lc-threshold ample preservation, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Positive ORIGINAL numerical dimension of a nef L constructs high-multiplicity
concentration divisors in a SINGLE explicitly chosen ample pencil lL+H, uniformly
for all high powers and all smooth closed points of a possibly singular source. No L-section, KV, Iitaka equality,
volume-growth premise, jet-surjectivity premise or concentration cut is supplied. -/
theorem positive_numerical_nef_ample_pencil_exists_smoothLocus_effective_concentration
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (hν : 1 ≤ cartierNumericalDimension K n hdim L H) (r : ℕ) :
    let l := n.factorial * (r + 1) ^ n + 1
    1 ≤ l ∧ CartierIsAmpleProj K (l • L + H) ∧
      ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∀ x : X, IsClosed {x} → x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus →
        ∃ M : CartierDivisor X, M.IsEffective ∧
          (∃ u : X.functionFieldˣ, M = j • (l • L + H) + principalCartierDivisor X u) ∧
          ∃ (g : X.functionFieldˣ) (z : X.presheaf.stalk x), z ≠ 0 ∧
            algebraMap (X.presheaf.stalk x) X.functionField z = (g : X.functionField) ∧
            M.IsLocalEquationAt x g ∧ ((r * j : ℕ) : ℕ∞) < localAdicOrder (X.presheaf.stalk x) z := by
  dsimp only
  let l := n.factorial * (r + 1) ^ n + 1
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hA := proper_nef_add_ample_isAmpleProj K (l • L) H (cartierIsNef_nsmul hL l) hH
  refine ⟨hl, hA, ?_⟩
  apply proper_ample_large_diagonal_exists_smoothLocus_effective_concentration_divisors K n hdim _ hA r
  have hdiag := positive_numerical_dimension_nef_pencil_diagonal_ge_parameter K n hdim hn L H hL hH hν l hl
  have hdiagR : (l : ℝ) ≤ (cartierMixedEulerDifference K (List.replicate n (l • L + H)) 0 : ℝ) := by
    exact_mod_cast hdiag
  apply (lt_div_iff₀ (show (0 : ℝ) < n.factorial by positivity)).mpr
  have hlR : ((r + 1 : ℕ) : ℝ) ^ n * n.factorial < (l : ℝ) := by
    dsimp [l]
    push_cast
    nlinarith
  exact hlR.trans_le hdiagR

end MixedFujita
