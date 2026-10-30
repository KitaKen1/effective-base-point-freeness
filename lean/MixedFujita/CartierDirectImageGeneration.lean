/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierBaseLocus
public import MixedFujita.ModuleLocalDirectImageGeneration
public import MixedFujita.AmpleTargetCartierPullbackIso
public import MixedFujita.ExceptionalCartierProjectionFormula

/-! 例外双有理モデルの生成開から元基底点除去。 See reports/check-243-base-locus-SNC-cut-basepoint-removal.json for the verified scope. Actual original Cartier base loci stabilize along powers. Stable-locus point removal for two coprime bases implies all large multiples generated. Usual KV lifts actual SNC-roundup cut generators and removes original basepoints. Usual KV and existence of required SNC data and cut generator remain explicit inputs; full klt BPF and F1/F2 remain unproved. -/

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


/-- Any generated point of an arbitrary direct-image target gives a point of the
ORIGINAL Cartier generation open, assuming only actual global section surjectivity. -/
theorem mem_cartierGenerationOpen_of_surjective_pushforward_generator
    {X Y : Scheme.{u}} [IsIntegral X] (φ : Y ⟶ X) (D : CartierDivisor X) (N : Y.Modules)
    (f : D.sheaf ⟶ (Scheme.Modules.pushforward φ).obj N)
    (hf : Function.Surjective (Scheme.Modules.Hom.app f ⊤))
    (y : Y) (W : Y.Opens) (hyW : y ∈ W)
    (d : N.over W ≅ SheafOfModules.unit (Y.ringCatSheaf.over W))
    (t : Γ(N, ⊤)) (ht : IsUnit (moduleOverFrameGlobalCoefficientGerm N W d y hyW t)) :
    φ y ∈ cartierGenerationOpen D := by
  let C := cartierEquationOpenCover D
  let : Nonempty (C.U (φ y)) := ⟨⟨φ y, C.mem (φ y)⟩⟩
  obtain ⟨s, hs⟩ := module_source_generator_of_surjective_pushforward_at_point φ D.sheaf N f hf y
    (C.U (φ y)) (C.mem (φ y))
    (cartierOpenFrameIso D (C.U (φ y)) (C.equation (φ y)) (C.equation_eq (φ y))) W hyW d t ht
  rw [moduleOverFrameGlobalCoefficientGerm_cartier] at hs
  exact (mem_cartierGenerationOpen_iff D (φ y)).mpr ⟨s,
    (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (φ y) _ _).mpr hs⟩


/-- An actual Cartier direct-image isomorphism reflects generation pointwise.
The source Cartier divisor need not be an actual pullback or have a section supplied. -/
theorem cartierGenerationOpen_le_preimage_of_pushforward_iso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X)
    (D : CartierDivisor X) (F : CartierDivisor Y)
    (a : D.sheaf ≅ (Scheme.Modules.pushforward φ).obj F.sheaf) :
    cartierGenerationOpen F ≤ φ ⁻¹ᵁ cartierGenerationOpen D := by
  intro y hy
  obtain ⟨t, ht⟩ := (mem_cartierGenerationOpen_iff F y).mp hy
  let C := cartierEquationOpenCover F
  let : Nonempty (C.U y) := ⟨⟨y, C.mem y⟩⟩
  apply mem_cartierGenerationOpen_of_surjective_pushforward_generator φ D F.sheaf a.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app a.hom ⊤)).surjective y
    (C.U y) (C.mem y) (cartierOpenFrameIso F (C.U y) (C.equation y) (C.equation_eq y)) t
  rw [moduleOverFrameGlobalCoefficientGerm_cartier]
  exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient F t y _ _).mp ht


/-- Model generators with an effective exceptional twist reflect ORIGINAL basepoint
removal. Projection formula and the all-Cartier pullback dictionary construct the isomorphism. -/
theorem proper_birational_exceptional_cartierGenerationOpen_le_preimage
    (K : Type u) [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p]
    (hp : Function.Bijective (dominantFunctionFieldMap p).hom)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hexc : ∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0) (D : CartierDivisor X) :
    cartierGenerationOpen (cartierPullback p D + E) ≤ p ⁻¹ᵁ cartierGenerationOpen D := by
  obtain ⟨aD⟩ := cartierPullback_sheaf_iso_modulePullback_of_ample_target K p H hH D
  let b : ((Scheme.Modules.pullback p).obj D.sheaf ⊗ E.sheaf) ≅
      (cartierPullback p D + E).sheaf := tensorIso aD (Iso.refl _) ≪≫ cartierTensorSheafIso _ _
  let a := effectiveExceptionalCartierTwistedPushforwardIso hnorm hnormT p hp E hE hexc D ≪≫
    (Scheme.Modules.pushforward p).mapIso b
  exact cartierGenerationOpen_le_preimage_of_pushforward_iso p D _ a

end MixedFujita
