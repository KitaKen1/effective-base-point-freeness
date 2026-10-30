/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCReducedAdjointClosedSubscheme
public import MixedFujita.LCNonKltKernelSupport

/-! KV不要の一意な被約非klt閉部分源と条件付き全随伴持ち上げ。 See reports/check-247-lc-non-klt-support-canonical-subscheme.json for the verified scope. The actual lc kernel image support equals the original all-model non-klt locus. Its radical coherent ideal and nonempty reduced lower-dimensional W are unique, independent of the SNC model and adjoint P, and constructed without KV. Containment in any closed Z is equivalent to klt outside Z. Usual KV is a condition only for simultaneous restriction lifting. Stable-base-locus perturbation, restricted-section nonvanishing, usual KV, normal minimal-lc-center adjunction, klt BPF and full F1/F2 remain unproved. -/

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



/-- The original effective lc non-klt pair constructs its UNIQUE reduced non-klt
closed subscheme, independent of both SNC model choices and adjoint Cartier P.
Containment in any prescribed closed set is equivalent to klt outside it. Usual KV
gives simultaneous actual restriction lifting for every nef-big adjoint. Nonvanishing
of restricted sections, usual KV itself, and klt BPF remain unproved. -/
theorem lc_pair_exists_unique_reduced_nonKlt_subscheme
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hlc : LogPairIsLogCanonical cX fX d D) (hnot : ¬ LogPairIsKlt cX fX d D) :
    ∃ I : X.IdealSheafData, I ≠ ⊥ ∧ Nonempty I.subscheme ∧
      genericPoint X ∉ (I.support : Set X) ∧ topologicalKrullDim I.subscheme ≤ (n - 1 : ℕ) ∧
      (idealSheafDataModule I).IsCoherent ∧ I.radical = I ∧ IsReduced I.subscheme ∧
      (1 : Γ(I.subscheme, ⊤)) ≠ 0 ∧
      (∀ x : X, x ∈ (I.support : Set X) ↔ ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX d D) ∧
      (∀ J : X.IdealSheafData, J.radical = J →
        (∀ x : X, x ∈ (J.support : Set X) ↔ ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX d D) → J = I) ∧
      (∀ Z : Closeds X, I.support ≤ Z ↔
        ∀ x : X, x ∉ Z → LogPairIsKltOverBasePoint (𝟙 X) x cX fX d D) ∧
      ∀ (_ : KawamataViehwegVanishingSNC K n),
      ∀ P : CartierDivisor X, CartierIsNef K (d • P - D) → CartierIsBig K (d • P - D) →
        Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1) ∧
        ∃ r : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
            ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf),
          Function.Surjective (Scheme.Modules.Hom.app r ⊤) ∧
          ∀ t : Γ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf, ⊤), t ≠ 0 →
            ∃ x : X, x ∈ (I.support : Set X) ∧ x ∉ cartierBaseLocus P := by
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
  let := (E - S).isInvertible_sheaf
  let : (E - S).sheaf.IsCoherent := invertible_module_isCoherent (E - S).sheaf
  let : IsAffineHom (pullback.diagonal (terminal.from T)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated (T ↘ Spec (CommRingCat.of K))
  have hNcoh := proper_module_pushforward_isCoherent p (E - S).sheaf
  let : IsIso (effectiveCartierPushforwardUnitMap p E hE) :=
    effectiveExceptionalCartierPushforwardUnitMap_isIso hnorm hnormT p hp E hE hexc
  let N := (Scheme.Modules.pushforward p).obj (E - S).sheaf
  let : N.IsCoherent := hNcoh
  let : N.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : N.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let j := cartierSubcutPushforwardUnitInclusion p E S hE hS
  let : Mono j := cartierSubcutPushforwardUnitInclusion_mono p E S hE hS
  have hC := nonzero_lc_critical_roundup_subcut_not_effective hnormT _ E S d hd hS hSne hSc hround
  have hunit : ¬ ∃ s : Γ(N, ⊤), Scheme.Modules.Hom.app j ⊤ s = (1 : Γ(X, ⊤)) := by
    intro hs
    exact hC ((one_in_global_range_cartierSubcutPushforwardUnitInclusion_iff p E S hE hS).mp hs)
  have hj : j ≠ 0 := cartierSubcutPushforwardUnitInclusion_ne_zero p hp hnormT E S hE hS
  let I := quasicoherentModuleImageIdealSheaf N j
  have hI : I ≠ ⊥ := fun h => hj ((quasicoherentModuleImageIdealSheaf_eq_bot_iff_map_zero N j).mp h)
  have hW := quasicoherentImageIdeal_subscheme_nonempty_of_unit_not_in_range N j hunit
  have hgeneric := integral_genericPoint_notMem_support_of_ideal_ne_bot I hI
  have hdimX : topologicalKrullDim X ≤ (n - 1 + 1 : ℕ) := by
    rw [Nat.sub_add_cancel hn]
    exact (etaleChart_topologicalKrullDim cX).le
  have hdim := quasicoherentImageIdeal_subscheme_dimension_le_predecessor N j hj (n - 1) hdimX
  let a : N ≅ idealSheafDataModule I := quasicoherentImageIdealModuleIso j
  have hIcoh : (idealSheafDataModule I).IsCoherent :=
    ⟨Scheme.Modules.isQuasicoherent_of_iso a, Scheme.Modules.isFiniteType_of_iso a⟩
  have hClo (t : CodimensionOnePoint T) : -1 ≤ cartierCoefficient (E - S) (t : T) := by
    rw [hround]
    exact lc_negative_boundary_roundup_ge_neg_one _ d hd
      (logPairIsLogCanonical_crepantBoundary_coefficient_le p hp cX fX d D hlc cT t)
  have hRad (U : X.affineOpens) : (I.ideal U).IsRadical :=
    canonical_subcut_image_ideal_affine_isRadical p hnormT E S hE hS hClo U
  have hIr : I.radical = I := by
    apply Scheme.IdealSheafData.ext
    funext U
    exact Ideal.radical_eq_iff.mpr (hRad U)
  have hWr : IsReduced I.subscheme := idealSheaf_subscheme_isReduced_of_affine_radical I hRad
  let := hWr
  let : Nonempty I.subscheme := hW
  have hOne : (1 : Γ(I.subscheme, ⊤)) ≠ 0 := one_ne_zero
  have hNK (x : X) : x ∈ (I.support : Set X) ↔
      ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX d D :=
    lc_canonical_subcut_image_support_iff_not_kltOverBasePoint p hp hnormT cX fX d hd D hlc
      cT ξ hinj hξ hsnc hsupp E S hE hS hround x
  have hUnique : ∀ J : X.IdealSheafData, J.radical = J →
      (∀ x : X, x ∈ (J.support : Set X) ↔ ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX d D) → J = I := by
    intro J hJr hJs
    have hsupport : J.support = I.support := SetLike.ext (fun x => (hJs x).trans (hNK x).symm)
    calc
      J = Scheme.IdealSheafData.vanishingIdeal J.support := by
        rw [Scheme.IdealSheafData.vanishingIdeal_support, hJr]
      _ = Scheme.IdealSheafData.vanishingIdeal I.support := congrArg _ hsupport
      _ = I := by rw [Scheme.IdealSheafData.vanishingIdeal_support, hIr]
  have hPlace : ∀ Z : Closeds X, I.support ≤ Z ↔
      ∀ x : X, x ∉ Z → LogPairIsKltOverBasePoint (𝟙 X) x cX fX d D := by
    classical
    intro Z
    constructor
    · intro h x hx
      by_contra hk
      exact hx (h ((hNK x).mpr hk))
    · intro h x hx
      by_contra hxZ
      exact ((hNK x).mp hx) (h x hxZ)
  refine ⟨I, hI, hW, hgeneric, hdim, hIcoh, hIr, hWr, hOne, hNK, hUnique, hPlace, ?_⟩
  intro hKV P hnef hbig
  have hvan := (crepant_roundup_subcut_H1_vanishing_of_usual_KV K hKV p hp hnorm H hH
    cX fX d hd D cT ξ hinj hξ hsnc hsupp E S hround P hnef hbig).2
  let : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ N) 1) := hvan
  have hIvan : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1) :=
    (actualCohomologyLinearEquivOfIso (tensorIso (Iso.refl P.sheaf) a) 1).symm.subsingleton
  let r := quasicoherentImageIdealCartierRestriction P N j
  have hr : Function.Surjective (Scheme.Modules.Hom.app r ⊤) :=
    quasicoherentImageIdealCartierRestriction_surjective_of_H1 P N j hvan
  refine ⟨hIvan, r, hr, ?_⟩
  intro t ht
  obtain ⟨y, hy⟩ := cartier_generator_at_image_of_nonzero_reduced_pullback_section I.subschemeι P r hr t ht
  refine ⟨I.subschemeι y, ?_, ?_⟩
  · rw [← I.range_subschemeι]
    exact ⟨y, rfl⟩
  · change ¬ ¬ I.subschemeι y ∈ cartierGenerationOpen P
    exact not_not.mpr hy

end MixedFujita
