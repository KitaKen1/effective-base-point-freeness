/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCRoundupCutGeneration
public import MixedFujita.KltAdjointH1Vanishing

/-! 通常KV・実SNC切断生成元から元基底点除去。 See reports/check-243-base-locus-SNC-cut-basepoint-removal.json for the verified scope. Actual original Cartier base loci stabilize along powers. Stable-locus point removal for two coprime bases implies all large multiples generated. Usual KV lifts actual SNC-roundup cut generators and removes original basepoints. Usual KV and existence of required SNC data and cut generator remain explicit inputs; full klt BPF and F1/F2 remain unproved. -/

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
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The geometric X-method endpoint: an ACTUAL SNC-roundup cut generator on a proper
birational model removes the ORIGINAL basepoint. Usual KV is the only vanishing input;
actual exceptional direct image and every Cartier pullback comparison are internal. -/
theorem original_basepoint_removed_of_usual_KV_snc_roundup_cut
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n)
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p]
    (hp : Function.Bijective (dominantFunctionFieldMap p).hom)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (D : CartierDivisor X) (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (B E S : CartierDivisor T)
    (hE : E.IsEffective)
    (hexc : ∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0) (hS : S.IsEffective) (d : ℕ) (hd : 1 ≤ d)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0)
    (hround : ∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉)
    (hnef : CartierIsNef K (d • (cartierPullback p D - smoothCanonicalDivisor cT) - B))
    (hbig : CartierIsBig K (d • (cartierPullback p D - smoothCanonicalDivisor cT) - B))
    (z : (effectiveCartierIdealSheaf S hS).subscheme)
    (W : (effectiveCartierIdealSheaf S hS).subscheme.Opens) (hzW : z ∈ W)
    (a : (((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj
      (cartierPullback p D + E).sheaf).over W) ≅
      SheafOfModules.unit ((effectiveCartierIdealSheaf S hS).subscheme.ringCatSheaf.over W))
    (t : Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj
      (cartierPullback p D + E).sheaf, ⊤))
    (ht : IsUnit (moduleOverFrameGlobalCoefficientGerm _ W a z hzW t)) :
    p ((effectiveCartierIdealSheaf S hS).subschemeι z) ∉ cartierBaseLocus D := by
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ y : T, IsIntegrallyClosed (T.presheaf.stalk y) :=
    fun y => smooth_stalk_isIntegrallyClosed (K := K) y
  have hsrc := snc_roundup_cut_generator_of_usual_KV K hKV cT ξ hinj hξ hsnc
    B E (cartierPullback p D) S hS d hd hsupport hround hnef hbig z W hzW a t ht
  have htarget := proper_birational_exceptional_cartierGenerationOpen_le_preimage K p hp
    hnorm hnormT H hH E hE hexc D hsrc
  exact fun h => h htarget

end MixedFujita
