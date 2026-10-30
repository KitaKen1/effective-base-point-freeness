/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NaturalRestrictionZeroDivisorSupport
public import MixedFujita.MinimalLCConcentrationDescent
public import MixedFujita.ConcentrationLCAmpleAdjoint

/-! 実切断の自然制限から元L随伴ample保持と極小中心降下。 See reports/check-258-minimal-lc-section-adjoint-descent.json for the verified scope. Inclusion-minimality and exterior LC force zero perturbation at every old critical prime, removing the all-old-center avoidance premise. Nonzero NATURAL restriction is equivalent to noncontainment in the actual zero-divisor support. The same threshold-prime strict old discrepancy places its center inside the original minimal center. An exact positive rational threshold and a lower-dimensional inclusion-minimal integral new-pair lc center are constructed internally. Actual original ample-adjoint sections preserve all-large ORIGINAL L ample adjoints. Exterior LC and an actual ambient non-LC point remain explicit hypotheses. Their construction from restricted concentration, appropriate center vanishing, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- For an ACTUAL section of the original ample adjoint pencil, NONZERO NATURAL
restriction to the original minimal center internally supplies the avoidance
needed above. The endpoint keeps an ample ORIGINAL L-adjoint in every large
degree and has a new inclusion-minimal integral lc center of smaller dimension.
Exterior lc and an actual ambient non-lc point are still explicit; constructing
a Bertini section with these properties and proving nonvanishing iteration is
not part of this conditional theorem. -/
theorem minimal_lc_center_section_descent_preserves_original_ample_adjoint
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (L : CartierDivisor X) (hL : CartierIsNef K L) (a₀ l j : ℕ) (hj : 1 ≤ j)
    (hA : CartierIsAmpleProj K ((d * a₀) • L - D))
    (s : Γ((j • ((l + d * a₀) • L - D)).sheaf, ⊤)) (hs : s ≠ 0)
    (hres : modulePullbackGlobalSections (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
      (j • ((l + d * a₀) • L - D)).sheaf s ≠ 0) (x : X)
    (hnonLC : ¬ LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d)
      (j • D + cartierSectionZeroDivisor (j • ((l + d * a₀) • L - D)) s hs))
    (houtside : ∀ y : X, y ∉ Z → LogPairIsLogCanonicalOverBasePoint (𝟙 X) y c f (j * d)
      (j • D + cartierSectionZeroDivisor (j • ((l + d * a₀) • L - D)) s hs))
    (k : ℕ) (hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (k + 1 : ℕ)) :
    let M := cartierSectionZeroDivisor (j • ((l + d * a₀) • L - D)) s hs
    ∃ a q : ℕ, 1 ≤ a ∧ 1 ≤ q ∧ d * a * j < q ∧
      LogPairBoundaryEffective c f (q * d) (q • D + (d * a) • M) ∧
      LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • M) ∧
      (¬ LogPairIsKlt c f (q * d) (q • D + (d * a) • M)) ∧
      (∀ m : ℕ, a₀ + a * j * l ≤ m →
        CartierIsAmpleProj K (((q * d) * m) • L - (q • D + (d * a) • M))) ∧
      ∃ W : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) W ∧
        (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f (q * d) (q • D + (d * a) • M) V → V ≤ W → V = W) ∧
        W < Z ∧ IsIntegral (Scheme.IdealSheafData.vanishingIdeal W).subscheme ∧
        topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal W).subscheme ≤ k := by
  classical
  let P := j • ((l + d * a₀) • L - D)
  let M := cartierSectionZeroDivisor P s hs
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let : IsIntegral I.subscheme := logCanonicalCenter_reduced_subscheme_isIntegral c f d D Z hZ
  have hIZ : I.support = Z := SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  have hZnot : ¬ Z ≤ (effectiveCartierIdealSheaf M (cartierSectionZeroDivisor_isEffective P s hs)).support := by
    rw [← hIZ]
    exact (natural_restriction_ne_zero_iff_not_le_zero_divisor_support (K := K) I P s hs).mp hres
  obtain ⟨a, q, ha, hq, hsmall, heff', hlc', hnot, _, W, hW, hminW, hWlt, _, hWi, hdimW⟩ :=
    minimal_lc_center_concentration_exists_strict_lower_dimensional_center hnorm c f d hd D heff Z hZ hmin
      M (cartierSectionZeroDivisor_isEffective P s hs) hZnot j hj x hnonLC houtside k hdim
  have hlinear : M = j • ((l + d * a₀) • L - D) + principalCartierDivisor X (cartierSectionUnit P s hs) := rfl
  have hamp := concentration_lc_perturbed_adjoint_isAmple K L D M hL d a₀ a q j l hsmall hA
    (cartierSectionUnit P s hs) hlinear
  exact ⟨a, q, ha, hq, hsmall, heff', hlc', hnot,
    fun m hm => original_nef_ample_adjoint_all_large K L _ hL (q * d) (a₀ + a * j * l) hamp m hm,
    W, hW, hminW, hWlt, hWi, hdimW⟩

end MixedFujita
