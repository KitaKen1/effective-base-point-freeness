/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.KltAdjointH1Vanishing

/-! 通常KVからモデル切断kernel・元の捻り直像kernelのH1消滅。 See reports/check-244-lc-critical-cut-roundup-kernel.json for the verified scope. Actual lc critical Cartier cuts and effective exceptional roundup parts are constructed. An original projective effective lc non-klt pair yields an internal smooth projective model, nonempty cut, coherent embedded kernel and usual-KV-based H1 vanishing and quotient section lifting. Usual KV and cut-generator existence remain unproved; the kernel is not identified with a reduced lc-center ideal; klt BPF and full F1/F2 remain incomplete. -/

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


/-- Usual KV annihilates both the ACTUAL crepant cut kernel on the model and its
Cartier-twisted ORIGINAL direct-image kernel. No local higher-direct-image vanishing
or reduced lc-center ideal identification is needed. The signed roundup is explicit. -/
theorem crepant_roundup_subcut_H1_vanishing_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n)
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p] [p.IsOver (Spec (CommRingCat.of K))]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover) (t : T) = 0)
    (E S : CartierDivisor T)
    (hround : ∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (P : CartierDivisor X) (hnef : CartierIsNef K (d • P - D)) (hbig : CartierIsBig K (d • P - D)) :
    Subsingleton (Scheme.Modules.Cohomology ((cartierPullback p P + E) - S).sheaf 1) ∧
      Subsingleton (Scheme.Modules.Cohomology
        (P.sheaf ⊗ (Scheme.Modules.pushforward p).obj (E - S).sheaf) 1) := by
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  let B := crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover
  let fT := crepantPullbackFormUnit p hp cX fX cT
  let Q := cartierPullback p P - principalCartierDivisor T fT
  have hadj : d • (Q - smoothCanonicalDivisor cT) - B = cartierPullback p (d • P - D) := by
    have hrec := crepantBoundaryCartier_smooth_recombine p hp cX fX d D cT
    dsimp [Q, B, fT]
    rw [cartierPullback_sub, cartierPullback_nsmul, ← hrec]
    module
  have hnefT : CartierIsNef K (d • (Q - smoothCanonicalDivisor cT) - B) := by
    rw [hadj]
    exact cartierIsNef_cartierPullback_of_ample hH hnef p
  have hbigT : CartierIsBig K (d • (Q - smoothCanonicalDivisor cT) - B) := by
    rw [hadj]
    exact cartierIsBig_cartierPullback hnorm hnormT p hp
      ((etaleChart_topologicalKrullDim cT).trans (etaleChart_topologicalKrullDim cX).symm) hbig
  let R := (cartierPullback p P + E) - S
  have hsrc := signed_snc_roundup_H1_vanishing_of_usual_KV K hKV cT ξ hinj hξ hsnc
    B (E - S) Q d hd hsupport hround hnefT hbigT
  have he : (Q + (E - S)) + principalCartierDivisor T fT = R := by dsimp [Q, R]; abel
  let b : (Q + (E - S)).sheaf ≅ R.sheaf :=
    (cartierSheafPrincipalShiftIso (Q + (E - S)) fT).symm ≪≫
      eqToIso (congrArg CartierDivisor.sheaf he)
  let : Subsingleton (Scheme.Modules.Cohomology (Q + (E - S)).sheaf 1) := hsrc
  have hR : Subsingleton (Scheme.Modules.Cohomology R.sheaf 1) :=
    (actualCohomologyLinearEquivOfIso b 1).symm.subsingleton
  obtain ⟨aP⟩ := cartierPullback_sheaf_iso_modulePullback_of_ample_target K p H hH P
  let a : ((Scheme.Modules.pullback p).obj P.sheaf ⊗ (E - S).sheaf) ≅ R.sheaf :=
    tensorIso aP (Iso.refl _) ≪≫ cartierTensorSheafIso _ _ ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (by dsimp [R]; abel))
  let : Subsingleton (Scheme.Modules.Cohomology R.sheaf 1) := hR
  have hM := (actualCohomologyLinearEquivOfIso a 1).subsingleton
  let := (E - S).isInvertible_sheaf
  let : (E - S).sheaf.IsCoherent := invertible_module_isCoherent _
  let : ((Scheme.Modules.pullback p).obj P.sheaf ⊗ (E - S).sheaf).IsCoherent :=
    cartierPulledTensor_isCoherent P p (E - S).sheaf
  refine ⟨hR, ?_⟩
  exact proper_module_H1_subsingleton_of_pushforward_iso K p _ _
    (cartierProjectionFormulaIso P p (E - S).sheaf) hM

end MixedFujita
