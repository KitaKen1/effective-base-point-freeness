/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentAmpleTwistGeneration
public import MixedFujita.FiniteFreeGlobalGenerators
public import MixedFujita.NoetherianIdealCoherence

/-! 非可逆実イデアルの全高次ample捻りの有限大域生成。 See reports/check-259-ample-ideal-generators-natural-corrections.json for the verified scope. All sufficiently high ORIGINAL ample Cartier twists of any actual coherent module are quotients of finite free sheaves, in every residue class. Actual noninvertible ideal modules are internally coherent and get finite canonical actual global generators. The canonical ideal inclusion pulls back to ZERO on its own actual closed subscheme by the actual adjunction mate. Arbitrary module tensor and NATURAL section restriction preserve this zero; finite ideal corrections preserve exact natural restriction and nonzero restricted sections even for nonreduced closed subschemes. Comparison of the finite ambient Cartier image family with center-exterior basepointfreeness, exterior LC/Bertini, ambient non-LC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Every actual ideal-sheaf module has an INTERNALLY coherent coefficient;
ALL high ORIGINAL ample twists have finite canonical global generators.
This works for noninvertible ideals on singular integral schemes. The
rank-one moduleIsGloballyGenerated definition is not used. -/
theorem locallyNoetherian_ideal_all_high_ample_twists_finite_global_generators
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) (I : X.IdealSheafData) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∃ (k : ℕ)
      (g : Fin k → Γ((b • A).sheaf ⊗ idealSheafDataModule I, ⊤)),
      Epi (biproduct.desc (fun i => CohomologyAux.homOfSection
        ((b • A).sheaf ⊗ idealSheafDataModule I) (g i))) := by
  let := locallyNoetherian_idealSheafDataModule_isCoherent I
  obtain ⟨b₀, hb₀⟩ := cartierIsAmpleProj_coherent_tensor_all_high_finite_free_epi A hA (idealSheafDataModule I)
  refine ⟨b₀, fun b hb => ?_⟩
  obtain ⟨k, π, hπ⟩ := hb₀ b hb
  let := hπ
  obtain ⟨g, hg⟩ := finite_free_epi_exists_canonical_global_generators k π
  exact ⟨k, g, hg⟩

end MixedFujita
