/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierDirectImageGeneration
public import MixedFujita.CartierCutEuler
public import MixedFujita.SignedSNCKawamataViehweg

/-! 通常KVと実roundup切断の一点生成元の持ち上げ。 See reports/check-243-base-locus-SNC-cut-basepoint-removal.json for the verified scope. Actual original Cartier base loci stabilize along powers. Stable-locus point removal for two coprime bases implies all large multiples generated. Usual KV lifts actual SNC-roundup cut generators and removes original basepoints. Usual KV and existence of required SNC data and cut generator remain explicit inputs; full klt BPF and F1/F2 remain unproved. -/

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


/-- A generating ACTUAL cut section lifts to a generator at its ambient image if the
kernel Cartier H1 vanishes. The cut may be nonreduced, reducible or nonproper. -/
theorem mem_cartierGenerationOpen_of_cut_H1_and_section_generator
    {X : Scheme.{u}} [IsIntegral X] (D S : CartierDivisor X) (hS : S.IsEffective)
    (hvan : Subsingleton (Scheme.Modules.Cohomology (D - S).sheaf 1))
    (z : (effectiveCartierIdealSheaf S hS).subscheme)
    (W : (effectiveCartierIdealSheaf S hS).subscheme.Opens) (hzW : z ∈ W)
    (d : (((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj D.sheaf).over W) ≅
      SheafOfModules.unit ((effectiveCartierIdealSheaf S hS).subscheme.ringCatSheaf.over W))
    (t : Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj D.sheaf, ⊤))
    (ht : IsUnit (moduleOverFrameGlobalCoefficientGerm _ W d z hzW t)) :
    (effectiveCartierIdealSheaf S hS).subschemeι z ∈ cartierGenerationOpen D := by
  apply mem_cartierGenerationOpen_of_surjective_pushforward_generator
    (effectiveCartierIdealSheaf S hS).subschemeι D _ (cartierCutShortComplex D S hS).g
    (Scheme.Modules.sections_surjective (cartierCutShortComplex_shortExact D S hS) hvan) z W hzW d t ht


/-- Usual SNC KV lifts a pointwise generating section of the ACTUAL cut after signed
roundup. The rounding divisor is E-S; E need not itself be the negative-boundary roundup. -/
theorem snc_roundup_cut_generator_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n)
    {T : Scheme.{u}} [IsIntegral T] [IsNoetherian T]
    [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (B E Q S : CartierDivisor T) (hS : S.IsEffective)
    (d : ℕ) (hd : 1 ≤ d)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0)
    (hround : ∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (d : ℝ))⌉)
    (hnef : CartierIsNef K (d • (Q - smoothCanonicalDivisor cT) - B))
    (hbig : CartierIsBig K (d • (Q - smoothCanonicalDivisor cT) - B))
    (z : (effectiveCartierIdealSheaf S hS).subscheme)
    (W : (effectiveCartierIdealSheaf S hS).subscheme.Opens) (hzW : z ∈ W)
    (a : (((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj (Q + E).sheaf).over W) ≅
      SheafOfModules.unit ((effectiveCartierIdealSheaf S hS).subscheme.ringCatSheaf.over W))
    (t : Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj (Q + E).sheaf, ⊤))
    (ht : IsUnit (moduleOverFrameGlobalCoefficientGerm _ W a z hzW t)) :
    (effectiveCartierIdealSheaf S hS).subschemeι z ∈ cartierGenerationOpen (Q + E) := by
  have hvan := signed_snc_roundup_H1_vanishing_of_usual_KV K hKV cT ξ hinj hξ hsnc
    B (E - S) Q d hd hsupport hround hnef hbig
  have he : Q + (E - S) = (Q + E) - S := by abel
  rw [he] at hvan
  exact mem_cartierGenerationOpen_of_cut_H1_and_section_generator (Q + E) S hS hvan z W hzW a t ht

end MixedFujita
