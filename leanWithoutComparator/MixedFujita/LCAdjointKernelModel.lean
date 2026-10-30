/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCRoundupExceptionalCut
public import MixedFujita.ExceptionalSubcutKernel
public import MixedFujita.LCRoundupKernelVanishing
public import MixedFujita.NonzeroEffectiveCartierCut
public import MixedFujita.HironakaSNCModelExistence

/-! 元lc非klt対から非空臨界切断・連接kernel・消滅と商切断全射。 See reports/check-244-lc-critical-cut-roundup-kernel.json for the verified scope. Actual lc critical Cartier cuts and effective exceptional roundup parts are constructed. An original projective effective lc non-klt pair yields an internal smooth projective model, nonempty cut, coherent embedded kernel and usual-KV-based H1 vanishing and quotient section lifting. Usual KV and cut-generator existence remain unproved; the kernel is not identified with a reduced lc-center ideal; klt BPF and full F1/F2 remain incomplete. -/

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


/-- From the ORIGINAL projective effective lc non-klt pair and an actual nef-big
adjoint, construct a smooth projective model, a NONEMPTY actual critical Cartier cut,
the effective exceptional roundup part, and a coherent kernel embedded in O_X.
Usual KV is the sole vanishing input. Models, roundups, cut nonemptiness, embeddings
and kernel H1 vanishing are not supplied. Existence of a cut generating section is
not asserted, nor is the kernel identified with a reduced lc-center ideal. -/
theorem lc_adjoint_exists_nonempty_critical_cut_and_kernel_vanishing_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hlc : LogPairIsLogCanonical cX fX d D) (hnot : ¬ LogPairIsKlt cX fX d D)
    (P : CartierDivisor X) (hnef : CartierIsNef K (d • P - D)) (hbig : CartierIsBig K (d • P - D)) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (_ : IsProper (T ↘ Spec (CommRingCat.of K)))
      (p : T ⟶ X) (_ : IsDominant p) (_ : p.IsOver (Spec (CommRingCat.of K))) (_ : IsProper p)
      (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
      (cT : EtaleChart K T n) (J E S : CartierDivisor T),
      CartierIsVeryAmpleProj K J ∧ E.IsEffective ∧ ∃ hS : S.IsEffective,
      S ≠ 0 ∧ Nonempty (effectiveCartierIdealSheaf S hS).subscheme ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient S (t : T) =
        if cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover)
          (t : T) = (d : ℤ) then 1 else 0) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover)
          (t : T) : ℝ) / (d : ℝ))⌉) ∧
      (∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 → cartierCoefficient E (t : T) = 0) ∧
      ((Scheme.Modules.pushforward p).obj (E - S).sheaf).IsCoherent ∧
      (∃ j : (Scheme.Modules.pushforward p).obj (E - S).sheaf ⟶ SheafOfModules.unit X.ringCatSheaf,
        Mono j ∧ Function.Surjective (Scheme.Modules.Hom.app
          (cokernel.π ((cartierTwistFunctor P).map j ≫ (rightUnitor P.sheaf).hom)) ⊤)) ∧
      Subsingleton (Scheme.Modules.Cohomology ((cartierPullback p P + E) - S).sheaf 1) ∧
      Subsingleton (Scheme.Modules.Cohomology
        (P.sheaf ⊗ (Scheme.Modules.pushforward p).obj (E - S).sheaf) 1) := by
  obtain ⟨H, hH⟩ := hProj
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, _, J, hJ⟩ :=
    exists_projective_snc_model_with_ample cX fX d D (fun i : PEmpty.{1} => i.elim) hH
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  have hTp : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  let := hTp
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨E, S, hE, hS, hSc, hround, hexc, hzero⟩ :=
    exists_effective_exceptional_lc_boundary_roundup_split p hp hnorm hcov cX fX d hd D heff hlc
      cT ξ hinj hξ hsnc hsupp
  have hSne : S ≠ 0 := fun h => hnot (hzero.mp h)
  have hSn := normal_nonzero_effectiveCartierCut_nonempty hnormT S hS hSne
  let := (E - S).isInvertible_sheaf
  let : (E - S).sheaf.IsCoherent := invertible_module_isCoherent (E - S).sheaf
  let : IsAffineHom (pullback.diagonal (terminal.from T)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated (T ↘ Spec (CommRingCat.of K))
  have hIcoh := proper_module_pushforward_isCoherent p (E - S).sheaf
  obtain ⟨j, hj⟩ := exceptional_subcut_pushforward_embeds_in_unit p hp hnorm hnormT E S hE hexc hS
  let := hj
  have hvan := crepant_roundup_subcut_H1_vanishing_of_usual_KV K hKV p hp hnorm H hH
    cX fX d hd D cT ξ hinj hξ hsnc hsupp E S hround P hnef hbig
  have hsurj := cartier_twisted_submodule_quotient_sections_surjective_of_H1 P _ j hvan.2
  exact ⟨T, hTi, hTo, hTN, hTs, hTp, p, hdom, hover, hprop, hp, cT, J, E, S,
    hJ, hE, hS, hSne, hSn, hSc, hround, hexc, hIcoh, ⟨j, hj, hsurj⟩, hvan⟩

end MixedFujita
