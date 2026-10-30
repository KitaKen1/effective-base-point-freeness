/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IntegralIdealNaturalRestriction
public import MixedFujita.NefCartierPullbackRepresentatives
public import MixedFujita.AmpleCartierPullbackRepresentatives
public import MixedFujita.SmoothLocusNefPencilConcentration

/-! 正の制限νの集中切断を同じ元ample pencilへ自然延長。 See reports/check-256-natural-center-concentration-extension.json for the verified scope. On proper integral targets a nonzero endomorphism of a Cartier line is an isomorphism, using the actual global-functions field and TauCeti global scalar action. Any section-surjective morphism to a restricted Cartier pushforward therefore implies surjectivity of the NATURAL restriction. Every actual ideal module on a locally Noetherian source is coherent. High ample powers restrict naturally and surjectively to integral closed sources and actual lc centers by unconditional Serre vanishing. In the positive restricted original numerical-dimension branch, all large powers of one original nef-ample pencil have nonzero ambient sections with naturally restricted sections of arbitrarily high linear order at every smooth closed point. No center normality, KV or initial original L-section is assumed. Original mL center lifting, appropriate center adjoint vanishing/nonvanishing, nu=0, center-exterior lc control and dimension descent, general KV, BPF and full F1/F2 remain unproved. -/

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


/-- Positive numerical dimension supplies actual high-order SECTIONS in one
explicit nef-ample pencil on a possibly singular integral proper source. -/
theorem positive_numerical_nef_ample_pencil_exists_smoothLocus_high_order_sections
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (hν : 1 ≤ cartierNumericalDimension K n hdim L H) (r : ℕ) :
    let l := n.factorial * (r + 1) ^ n + 1
    1 ≤ l ∧ CartierIsAmpleProj K (l • L + H) ∧
      ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∀ x : X, IsClosed {x} →
        x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus →
        ∃ s : Γ((j • (l • L + H)).sheaf, ⊤), s ≠ 0 ∧
          ((r * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder (j • (l • L + H)) x s := by
  dsimp only
  let l := n.factorial * (r + 1) ^ n + 1
  have hl : 1 ≤ l := by dsimp [l]; omega
  have hA := proper_nef_add_ample_isAmpleProj K (l • L) H (cartierIsNef_nsmul hL l) hH
  refine ⟨hl, hA, ?_⟩
  apply proper_ample_large_diagonal_exists_smoothLocus_high_order_sections K n hdim _ hA r
  have hdiag := positive_numerical_dimension_nef_pencil_diagonal_ge_parameter K n hdim hn L H hL hH hν l hl
  have hdiagR : (l : ℝ) ≤ (cartierMixedEulerDifference K (List.replicate n (l • L + H)) 0 : ℝ) := by
    exact_mod_cast hdiag
  apply (lt_div_iff₀ (show (0 : ℝ) < n.factorial by positivity)).mpr
  have hlR : ((r + 1 : ℕ) : ℝ) ^ n * n.factorial < (l : ℝ) := by
    dsimp [l]
    push_cast
    nlinarith
  exact hlR.trans_le hdiagR


/-- On an integral closed source of positive restricted numerical dimension,
all large powers of ONE original nef-ample pencil have actual ambient sections
whose NATURAL restrictions have arbitrarily prescribed linear high order.
Center normality, KV and an initial original L-section are not assumptions. -/
theorem integral_closed_positive_numerical_pencil_lifts_high_order_sections
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (I : X.IdealSheafData) [IsIntegral I.subscheme]
    [I.subscheme.Over (Spec (CommRingCat.of K))] [I.subschemeι.IsOver (Spec (CommRingCat.of K))]
    [IsProper (I.subscheme ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim I.subscheme = n) (hn : 1 ≤ n)
    (L H : CartierDivisor X) (hL : CartierIsNef K L) (hH : CartierIsAmpleProj K H)
    (LZ HZ : CartierDivisor I.subscheme)
    (aL : (Scheme.Modules.pullback I.subschemeι).obj L.sheaf ≅ LZ.sheaf)
    (aH : (Scheme.Modules.pullback I.subschemeι).obj H.sheaf ≅ HZ.sheaf)
    (hν : 1 ≤ cartierNumericalDimension K n hdim LZ HZ) (r : ℕ) :
    let l := n.factorial * (r + 1) ^ n + 1
    CartierIsAmpleProj K (l • L + H) ∧
      ∃ a : (Scheme.Modules.pullback I.subschemeι).obj (l • L + H).sheaf ≅ (l • LZ + HZ).sheaf,
        ∃ j₀ : ℕ, 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∀ x : I.subscheme, IsClosed {x} →
          x ∈ (I.subscheme ↘ Spec (CommRingCat.of K)).smoothLocus →
          ∃ s : Γ((j • (l • L + H)).sheaf, ⊤), s ≠ 0 ∧
            let t := cartierPullbackGlobalSectionViaIso (j • (l • L + H)) I.subschemeι
              (j • (l • LZ + HZ)) (cartierPullbackGradedIso (l • L + H) I.subschemeι (l • LZ + HZ) a j) s
            t ≠ 0 ∧ ((r * j : ℕ) : ℕ∞) < cartierSectionVanishingOrder (j • (l • LZ + HZ)) x t := by
  dsimp only
  let l := n.factorial * (r + 1) ^ n + 1
  let : IsProper (I.subscheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := I.subschemeι)]
    infer_instance
  have hLZ := cartierIsNef_of_pullback_representative K I.subschemeι L LZ aL hL
  have hHZ := cartierIsAmpleProj_of_finite_pullback_over K I.subschemeι H HZ hH aH
  obtain ⟨_, _, j₁, hj₁, hsec⟩ :=
    positive_numerical_nef_ample_pencil_exists_smoothLocus_high_order_sections K n hdim hn LZ HZ hLZ hHZ hν r
  have hA := proper_nef_add_ample_isAmpleProj K (l • L) H (cartierIsNef_nsmul hL l) hH
  let a : (Scheme.Modules.pullback I.subschemeι).obj (l • L + H).sheaf ≅ (l • LZ + HZ).sheaf :=
    (Scheme.Modules.pullback I.subschemeι).mapIso (cartierTensorSheafIso (l • L) H).symm ≪≫
      cartierPullbackTensorIso (l • L) I.subschemeι H.sheaf ≪≫
        tensorIso (cartierPullbackGradedIso L I.subschemeι LZ aL l) aH ≪≫ cartierTensorSheafIso (l • LZ) HZ
  obtain ⟨j₂, hrest⟩ := integral_ideal_subscheme_all_high_ample_twists_natural_restriction K I (l • L + H) hA
  refine ⟨hA, a, max j₁ j₂, hj₁.trans (le_max_left _ _), ?_⟩
  intro j hj x hx hxsm
  obtain ⟨t, ht, hord⟩ := hsec j ((le_max_left _ _).trans hj) x hx hxsm
  let e := cartierPullbackGradedIso (l • L + H) I.subschemeι (l • LZ + HZ) a j
  have he := (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom ⊤)).surjective
  have hsurj := he.comp ((hrest j ((le_max_right _ _).trans hj)).2)
  obtain ⟨s, hs⟩ := hsurj t
  have hsne : s ≠ 0 := by
    intro hz
    apply ht
    simpa only [hz, Function.comp_apply, map_zero] using hs.symm
  refine ⟨s, hsne, ?_⟩
  change cartierPullbackGlobalSectionViaIso (j • (l • L + H)) I.subschemeι (j • (l • LZ + HZ)) e s ≠ 0 ∧ _
  have hst : cartierPullbackGlobalSectionViaIso (j • (l • L + H)) I.subschemeι (j • (l • LZ + HZ)) e s = t := hs
  rw [hst]
  exact ⟨ht, hord⟩

end MixedFujita
