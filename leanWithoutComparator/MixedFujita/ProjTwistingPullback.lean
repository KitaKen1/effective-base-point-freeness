/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGATwistPullbackIso
public import SGA.Foundations.Projective.TwistingSheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! Graded maps preserve the actual fraction sections and transition units
of Serre twisting bundles. Consequently every integer twist commutes with the
actual module pullback under Proj of a graded map. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Graded
open scoped HomogeneousIdeal
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

theorem projMap_appLE_fracSection {d : ℕ} {a b : A} (ha : a ∈ 𝒜 d) (hb : b ∈ 𝒜 d)
    (U : (Proj 𝒜).Opens) (V : (Proj ℬ).Opens) (hU : U ≤ Proj.basicOpen 𝒜 b)
    (hV : V ≤ Proj.map φ hφ ⁻¹ᵁ U) :
    (Proj.map φ hφ).appLE U V hV (Proj.fracSection 𝒜 ha hb U hU) =
      Proj.fracSection ℬ (map_mem φ ha) (map_mem φ hb) V
        (hV.trans ((Proj.map φ hφ).preimage_mono hU)) := by
  apply Subtype.ext
  funext x
  change HomogeneousLocalization.mk _ = .mk _
  ext; simp

variable {ι : Type u} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1)
  (hcov : ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤)

include hφ hcov in
theorem projMap_image_degreeOne_cover :
    ⨆ i, Proj.basicOpen ℬ (φ (f i)) = ⊤ := by
  simp only [← Proj.map_preimage_basicOpen φ hφ, ← Scheme.Hom.preimage_iSup,
    hcov, Scheme.Hom.preimage_top]

theorem projTwistingSheaf_pullback :
    (Proj.twistingSheaf 𝒜 f hf hcov).pullback (Proj.map φ hφ) =
      Proj.twistingSheaf ℬ (fun i => φ (f i)) (fun i => map_mem φ (hf i))
        (projMap_image_degreeOne_cover φ hφ f hcov) := by
  simp only [Scheme.LineBundle.pullback, Proj.twistingSheaf, Proj.map_preimage_basicOpen]
  congr 1

noncomputable def projTwistingModulePullbackIso (d : ℤ) :
    (Scheme.Modules.pullback (Proj.map φ hφ)).obj
        ((Proj.twistingSheaf 𝒜 f hf hcov).toModules d) ≅
      (Proj.twistingSheaf ℬ (fun i => φ (f i)) (fun i => map_mem φ (hf i))
        (projMap_image_degreeOne_cover φ hφ f hcov)).toModules d :=
  sgaLineBundlePullbackPowerIso _ _ d ≪≫
    eqToIso (congrArg (fun L => L.toModules d) (projTwistingSheaf_pullback φ hφ f hf hcov))

end MixedFujita
