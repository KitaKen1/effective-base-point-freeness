/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealSheafCartierSectionLifting
public import MixedFujita.CoherentAmpleSerreVanishing

/-! 連接実閉部分源の高ampleねじり全高次Serreと制限切断全射。 See reports/check-250-BPF-ample-boundary-concentration-extension.json for the verified scope. Original nef-big BPF data internally yield a small effective klt boundary increase with an ample adjoint, retaining L and a0. High-power lc adjoints stay ample for all large degrees. Every coherent ideal subscheme has unconditional full Serre vanishing and actual restriction lifting for high ample twists. The fixed nonempty reduced base source and these concentration-twist extensions are internal. Original L lifting still needs explicit usual KV. Initial and restricted L-nonvanishing, minimal-center normality/vanishing, high-multiplicity concentration, usual KV, BPF and full F1/F2 remain unproved. -/

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






/-- All high AMPLE-adjoint twists have full positive ideal cohomology vanishing
and actual restriction surjectivity to ANY coherent ideal-sheaf subscheme.
This is unconditional Serre vanishing, with no usual-KV or reducedness input. -/
theorem ample_ideal_subscheme_all_high_twists_serre_and_restriction
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A)
    (I : X.IdealSheafData) [(idealSheafDataModule I).IsCoherent] :
    ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
      (∀ q : ℕ, Subsingleton (Scheme.Modules.Cohomology ((b • A).sheaf ⊗ idealSheafDataModule I) (q + 1))) ∧
      ∃ r : (b • A).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj (b • A).sheaf),
        Function.Surjective (Scheme.Modules.Hom.app r ⊤) := by
  obtain ⟨b₀, hb₀⟩ := cartierIsAmpleProj_coherent_tensor_serreVanishing A hA (idealSheafDataModule I)
  exact ⟨b₀, fun b hb => ⟨hb₀ b hb, idealSheaf_cartier_restriction_exists_surjective_of_H1
    (b • A) I (hb₀ b hb 0)⟩⟩

end MixedFujita
