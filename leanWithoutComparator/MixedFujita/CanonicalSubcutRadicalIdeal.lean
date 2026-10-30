/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalSubcutFunctionCriterion
public import MixedFujita.NormalCartierPowerRoot
public import MixedFujita.LCRoundupSplitArithmetic
public import MixedFujita.QuasicoherentImageIdealSheaf
public import MixedFujita.DominantCartierPullback

/-! lc roundup係数下限と実kernel像アフィンイデアルの根基性。 See reports/check-246-lc-radical-reduced-fixed-subscheme-lifting.json for the verified scope. The actual lc kernel image ideal is radical and its nonempty lower-dimensional subscheme W is reduced. One fixed I and W works for all nef-big adjoints. Usual KV gives actual restriction section lifting; any nonzero restricted section removes an original basepoint on W. Usual KV itself, restricted-section nonvanishing and stable-base-locus placement remain unproved; no normal lc-center adjunction, klt BPF or full F1/F2 is claimed. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Every lc negative-boundary roundup coefficient is at least -1. -/
theorem lc_negative_boundary_roundup_ge_neg_one (b : ℤ) (d : ℕ) (hd : 1 ≤ d)
    (hb : b ≤ (d : ℤ)) : -1 ≤ ⌈-((b : ℝ) / (d : ℝ))⌉ := by
  have h := lc_roundup_positive_part_nonneg b d hd hb
  split_ifs at h <;> omega


/-- The actual affine image ideals of a canonical subcut kernel are radical when
the kernel Cartier coefficients are at least -1. No lc-center or radicality input is used. -/
theorem canonical_subcut_image_ideal_affine_isRadical
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    (p : T ⟶ X) [IsDominant p]
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    [((Scheme.Modules.pushforward p).obj (E - S).sheaf).IsQuasicoherent]
    (hC : ∀ t : CodimensionOnePoint T, -1 ≤ cartierCoefficient (E - S) (t : T))
    (U : X.affineOpens) :
    ((quasicoherentModuleImageIdealSheaf ((Scheme.Modules.pushforward p).obj (E - S).sheaf)
      (cartierSubcutPushforwardUnitInclusion p E S hE hS)).ideal U).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by omega)).mpr
  intro a ha
  change ∃ s, Scheme.Modules.Hom.app (cartierSubcutPushforwardUnitInclusion p E S hE hS) U.1 s = a
  by_cases hU : Nonempty U.1
  · let := hU
    let := dominant_preimage_nonempty p U.1
    have hm := (function_in_range_cartierSubcutPushforwardUnitInclusion_iff p E S hE hS U.1
      (a ^ 2)).mp ha
    have hroot := normal_cartier_regular_power_root_mem_sections hnormT (E - S) hC
      (p ⁻¹ᵁ U.1) ((p.app U.1).hom a) 2 (by simpa only [map_pow] using hm)
    exact (function_in_range_cartierSubcutPushforwardUnitInclusion_iff p E S hE hS U.1 a).mpr hroot
  · have hbot : U.1 = ⊥ := (Opens.not_nonempty_iff_eq_bot U.1).mp
      (fun ⟨x, hx⟩ => hU ⟨⟨x, hx⟩⟩)
    let : Subsingleton Γ(SheafOfModules.unit X.ringCatSheaf, U.1) :=
      abelianSheaf_empty_sections_subsingleton
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf)) hbot
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _

end MixedFujita
