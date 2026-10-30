/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InfinitesimalThickeningSubscheme
public import MixedFujita.InfinitesimalLayerAffineSheaf
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Exceptional

/-! Actual sheaf layers on Proj of the Rees algebra of an ideal.
The exceptional ideal and its regular chart equations are constructed by
the pinned blow-up library. All quotient thickenings and associated-graded
layers have global presentations; local kernel coordinates need no supplied
principalization or degreewise sheaf isomorphism. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] (I : Ideal R)

noncomputable def affineBlowUpInfinitesimalChart (a : I) : (affineBlowUp I).affineOpens :=
  ⟨(affineBlowUp.chart I a).opensRange, isAffineOpen_opensRange _⟩

noncomputable def affineBlowUpInfinitesimalEquation (a : I) :
    Γ(affineBlowUp I, (affineBlowUpInfinitesimalChart I a).1) :=
  Classical.choose (affineBlowUp.exists_generator_exceptionalIdeal_opensRange_chart I a)

theorem affineBlowUpInfinitesimalEquation_regular (a : I) :
    affineBlowUpInfinitesimalEquation I a ∈
      nonZeroDivisors Γ(affineBlowUp I, (affineBlowUpInfinitesimalChart I a).1) :=
  (Classical.choose_spec
    (affineBlowUp.exists_generator_exceptionalIdeal_opensRange_chart I a)).1

theorem affineBlowUpInfinitesimalEquation_ideal (a : I) :
    I.map (structMapV (affineBlowUp.π I) (affineBlowUpInfinitesimalChart I a).1) =
      Ideal.span {affineBlowUpInfinitesimalEquation I a} := by
  rw [← infinitesimalBaseIdealSheaf_affine]
  exact (Classical.choose_spec
    (affineBlowUp.exists_generator_exceptionalIdeal_opensRange_chart I a)).2

variable [IsNoetherianRing R]

noncomputable def affineBlowUpActualLayerSectionsEquiv (a : I) (n : ℕ) :
    (Γ(affineBlowUp I, (affineBlowUpInfinitesimalChart I a).1) ⧸
      I.map (structMapV (affineBlowUp.π I) (affineBlowUpInfinitesimalChart I a).1))
      ≃ₗ[Γ(affineBlowUp I, (affineBlowUpInfinitesimalChart I a).1)]
      Γ(infinitesimalCohomologyLayer (affineBlowUp.π I) I (unitModule (affineBlowUp I)) n,
        (affineBlowUpInfinitesimalChart I a).1) :=
  unitInfinitesimalLayerRegularSectionsEquiv (affineBlowUp.π I) I
    (affineBlowUpInfinitesimalChart I a) (affineBlowUpInfinitesimalEquation I a)
    (affineBlowUpInfinitesimalEquation_ideal I a) (affineBlowUpInfinitesimalEquation_regular I a) n

theorem affineBlowUpActualLayerSectionsEquiv_inclusion_mk (a : I) (n : ℕ)
    (x : Γ(affineBlowUp I, (affineBlowUpInfinitesimalChart I a).1)) :
    (kernel.ι ((unitModule (affineBlowUp I)).quotientIdealPowMap (affineBlowUp.π I) I n)).app
        (affineBlowUpInfinitesimalChart I a).1
        (affineBlowUpActualLayerSectionsEquiv I a n (Submodule.Quotient.mk x)) =
      ((unitModule (affineBlowUp I)).toQuotientIdealPow (affineBlowUp.π I) I (n + 1)).app
        (affineBlowUpInfinitesimalChart I a).1
        ((affineBlowUpInfinitesimalEquation I a) ^ (n + 1) * x) :=
  unitInfinitesimalLayerRegularSectionsEquiv_inclusion_mk _ _ _ _ _ _ _ _

noncomputable def affineBlowUpActualLayerChartIso (a : I) (n : ℕ) :
    (infinitesimalCohomologyLayer (affineBlowUp.π I) I (unitModule (affineBlowUp I)) n).restrict
        (affineBlowUpInfinitesimalChart I a).2.fromSpec ≅
      tilde (ModuleCat.of Γ(affineBlowUp I, (affineBlowUpInfinitesimalChart I a).1)
        (Γ(affineBlowUp I, (affineBlowUpInfinitesimalChart I a).1) ⧸
          I.map (structMapV (affineBlowUp.π I) (affineBlowUpInfinitesimalChart I a).1))) :=
  unitInfinitesimalLayerRegularSheafIso (affineBlowUp.π I) I
    (affineBlowUpInfinitesimalChart I a) (affineBlowUpInfinitesimalEquation I a)
    (affineBlowUpInfinitesimalEquation_ideal I a) (affineBlowUpInfinitesimalEquation_regular I a) n

/-- Every point has one chart presenting all actual infinitesimal layers. -/
theorem affineBlowUp_actual_layers_affine_cover (x : affineBlowUp I) :
    ∃ U : (affineBlowUp I).affineOpens, x ∈ U.1 ∧ ∀ n : ℕ,
      Nonempty ((infinitesimalCohomologyLayer (affineBlowUp.π I) I
          (unitModule (affineBlowUp I)) n).restrict U.2.fromSpec ≅
        tilde (ModuleCat.of Γ(affineBlowUp I, U.1)
          (Γ(affineBlowUp I, U.1) ⧸ I.map (structMapV (affineBlowUp.π I) U.1)))) := by
  obtain ⟨a, ha⟩ := affineBlowUp.exists_mem_opensRange_chart I x
  exact ⟨affineBlowUpInfinitesimalChart I a, ha, fun n => ⟨affineBlowUpActualLayerChartIso I a n⟩⟩

/-- A global presentation on the actual blow-up by powers of its exceptional ideal. -/
noncomputable def affineBlowUpActualLayerGlobalIso (n : ℕ) :
    infinitesimalCohomologyLayer (affineBlowUp.π I) I (unitModule (affineBlowUp I)) n ≅
      cokernel (idealSheafDataModuleMap
        (idealSheafPower_le_succ (affineBlowUp.exceptionalIdeal I) (n + 1))) :=
  infinitesimalLayerIdealSheafQuotientIso (affineBlowUp.π I) I n

/-- The actual quotient is the structure sheaf of the actual exceptional thickening. -/
noncomputable def affineBlowUpActualThickeningIso (n : ℕ) :
    (unitModule (affineBlowUp I)).quotientIdealPow (affineBlowUp.π I) I n ≅
      (Scheme.Modules.pushforward ((affineBlowUp.exceptionalIdeal I) ^ (n + 1)).subschemeι).obj
        (unitModule ((affineBlowUp.exceptionalIdeal I) ^ (n + 1)).subscheme) :=
  infinitesimalQuotientIdealSubschemeIso (affineBlowUp.π I) I n

theorem affineBlowUpActualThickeningIso_quotient (n : ℕ) :
    (unitModule (affineBlowUp I)).toQuotientIdealPow (affineBlowUp.π I) I n ≫
        (affineBlowUpActualThickeningIso I n).hom =
      schemeUnitToPushforwardUnit ((affineBlowUp.exceptionalIdeal I) ^ (n + 1)).subschemeι :=
  infinitesimalQuotientIdealSubschemeIso_quotient (affineBlowUp.π I) I n

noncomputable def affineBlowUpActualExceptionalQuotientIso :
    (unitModule (affineBlowUp I)).quotientIdealPow (affineBlowUp.π I) I 0 ≅
      (Scheme.Modules.pushforward (affineBlowUp.exceptionalIdeal I).subschemeι).obj
        (unitModule (affineBlowUp.exceptionalIdeal I).subscheme) :=
  affineBlowUpActualThickeningIso I 0 ≪≫
    eqToIso (congrArg (fun J : (affineBlowUp I).IdealSheafData =>
      (Scheme.Modules.pushforward J.subschemeι).obj (unitModule J.subscheme))
      (pow_one (affineBlowUp.exceptionalIdeal I)))

end MixedFujita
