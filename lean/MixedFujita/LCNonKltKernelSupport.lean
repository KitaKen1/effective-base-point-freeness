/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalSubcutSupport
public import MixedFujita.LCCriticalRoundupSupportArithmetic
public import MixedFujita.CrepantSNCBasePointKlt
public import MixedFujita.CrepantSNCBasePointLogCanonical

/-! 実lc kernel像の台と元の全モデル非klt点集合の同定。 See reports/check-247-lc-non-klt-support-canonical-subscheme.json for the verified scope. The actual lc kernel image support equals the original all-model non-klt locus. Its radical coherent ideal and nonempty reduced lower-dimensional W are unique, independent of the SNC model and adjoint P, and constructed without KV. Containment in any closed Z is equivalent to klt outside Z. Usual KV is a condition only for simultaneous restriction lifting. Stable-base-locus perturbation, restricted-section nonvanishing, usual KV, normal minimal-lc-center adjunction, klt BPF and full F1/F2 remain unproved. -/

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



/-- On an actual lc SNC model, the canonical kernel support is EXACTLY the original
all-model non-klt locus. The equivalence uses the existing base-point SNC comparison. -/
theorem lc_canonical_subcut_image_support_iff_not_kltOverBasePoint
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))] [IsProper p]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical cX fX d D)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover) (t : T) = 0)
    (E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective)
    [IsIso (effectiveCartierPushforwardUnitMap p E hE)]
    [((Scheme.Modules.pushforward p).obj (E - S).sheaf).IsQuasicoherent]
    (hround : ∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) (x : X) :
    x ∈ ((quasicoherentModuleImageIdealSheaf ((Scheme.Modules.pushforward p).obj (E - S).sheaf)
      (cartierSubcutPushforwardUnitInclusion p E S hE hS)).support : Set X) ↔
      ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX d D := by
  classical
  rw [canonical_subcut_image_support_iff_negative_prime p hnormT E S hE hS x]
  rw [logPairIsKltOverBasePoint_iff_crepant_snc_coefficients p hp (𝟙 X) x
    cX fX d hd D cT ξ hinj hξ hsnc hsupport]
  simp only [Category.comp_id]
  push Not
  constructor
  · rintro ⟨t, hxt, ht⟩
    have hb := logPairIsLogCanonical_crepantBoundary_coefficient_le p hp cX fX d D hlc cT t
    rw [hround, lc_negative_boundary_roundup_negative_iff_critical _ d hd hb] at ht
    have hin : (t : T) ∈ Set.range ξ := by
      by_contra hn
      have hzero := hsupport t hn
      omega
    obtain ⟨i, hi⟩ := hin
    refine ⟨i, ?_, ?_⟩
    · simpa only [hi] using hxt
    · simpa only [hi, ht] using (le_refl (d : ℤ))
  · rintro ⟨i, hxi, hi⟩
    let t : CodimensionOnePoint T := ⟨ξ i, hξ i⟩
    have hb := logPairIsLogCanonical_crepantBoundary_coefficient_le p hp cX fX d D hlc cT t
    refine ⟨t, hxi, ?_⟩
    rw [hround, lc_negative_boundary_roundup_negative_iff_critical _ d hd hb]
    exact le_antisymm hb hi

end MixedFujita
