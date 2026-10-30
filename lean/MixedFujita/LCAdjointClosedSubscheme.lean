/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCAdjointKernelModel
public import MixedFujita.BirationalCartierGenericUnit
public import MixedFujita.QuasicoherentImageIdealQuotient
public import MixedFujita.ImageIdealCartierRestriction
public import MixedFujita.LCCriticalSubcutProper

/-! 元lc随伴データから非空低次元閉部分源と実制限切断の持ち上げ。 See reports/check-245-lc-kernel-closed-subscheme-lifting.json for the verified scope. The canonical lc kernel gives a proper nonzero actual image ideal, a concrete nonzero untwisted quotient unit, and a nonempty lower-dimensional actual closed subscheme W. Usual KV gives actual Cartier restriction section lifting to W. Usual KV itself and nonzero/generating sections of P restricted to W remain unproved; W is not identified with a reduced lc center; klt BPF and full F1/F2 remain incomplete. -/

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


/-- The ORIGINAL lc non-klt nef-big adjoint problem produces an actual nonempty
proper closed subscheme of smaller dimension, its actual coherent ideal, and actual
Cartier restriction surjectivity. Even its structure unit is a nonzero global section.
Usual KV remains an explicit input; no nonzero section of P restricted to this
subscheme is asserted, and no reduced lc-center identification is assumed. -/
theorem lc_adjoint_exists_nonempty_lower_dimensional_subscheme_lifting_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n) (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hlc : LogPairIsLogCanonical cX fX d D) (hnot : ¬ LogPairIsKlt cX fX d D)
    (P : CartierDivisor X) (hnef : CartierIsNef K (d • P - D)) (hbig : CartierIsBig K (d • P - D)) :
    ∃ I : X.IdealSheafData, I ≠ ⊥ ∧ Nonempty I.subscheme ∧
      genericPoint X ∉ (I.support : Set X) ∧ topologicalKrullDim I.subscheme ≤ (n - 1 : ℕ) ∧
      (idealSheafDataModule I).IsCoherent ∧ (1 : Γ(I.subscheme, ⊤)) ≠ 0 ∧
      Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1) ∧
      ∃ r : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf),
        Function.Surjective (Scheme.Modules.Hom.app r ⊤) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, hTp, p, hdom, hover, hprop, hp, cT, _, E, S,
      _, hE, hS, hSne, _, hSc, hround, hexc, hNcoh, _, _, hvan⟩ :=
    lc_adjoint_exists_nonempty_critical_cut_and_kernel_vanishing_of_usual_KV K hKV
      hnorm hcov hProj cX fX d hd D heff hlc hnot P hnef hbig
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hTp
  let := hdom
  let := hover
  let := hprop
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
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
  let : Nonempty I.subscheme := hW
  have hOne : (1 : Γ(I.subscheme, ⊤)) ≠ 0 := one_ne_zero
  let : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ N) 1) := hvan
  have hIvan : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1) :=
    (actualCohomologyLinearEquivOfIso (tensorIso (Iso.refl P.sheaf) a) 1).symm.subsingleton
  exact ⟨I, hI, hW, hgeneric, hdim, hIcoh, hOne, hIvan,
    quasicoherentImageIdealCartierRestriction P N j,
    quasicoherentImageIdealCartierRestriction_surjective_of_H1 P N j hvan⟩

end MixedFujita
