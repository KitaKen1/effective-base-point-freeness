/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierInfinitesimalTwist
public import MixedFujita.ProjectiveInfinitesimalLayerVanishing
public import MixedFujita.SGACartierTwistPowers

/-! Actual Cartier restrictions on closed thickenings give a finite-thickness
vanishing criterion. A single projective restriction model transfers every
structure-sheaf layer model to the corresponding Cartier layer. The structure
layer models themselves remain explicit geometric hypotheses. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory MonoidalCategory Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable {A : CommRingCat.{u}} {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec A) (I : Ideal A) (D : CartierDivisor X)

theorem proper_cartier_cohomology_vanish_of_sufficiently_thick_restriction
    [IsNoetherianRing A] [IsProper f] [D.sheaf.IsCoherent]
    (hI : I ≤ Ideal.jacobson ⊥) (q : ℕ) :
    ∃ c : ℕ, ∀ n ≥ c,
      Subsingleton (Scheme.Modules.Cohomology
        ((Scheme.Modules.pullback ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subschemeι).obj
          D.sheaf) q) →
      Subsingleton (Scheme.Modules.Cohomology D.sheaf q) := by
  obtain ⟨c, hc⟩ := proper_cohomology_vanish_of_sufficiently_thick_quotient I hI f D.sheaf q
  refine ⟨c, fun n hn hv ↦ hc n hn ?_⟩
  let := hv
  let : Subsingleton (Scheme.Modules.Cohomology
      ((Scheme.Modules.pushforward ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subschemeι).obj
        ((Scheme.Modules.pullback ((infinitesimalBaseIdealSheaf f I) ^ (n + 1)).subschemeι).obj
          D.sheaf)) q) :=
    (closedImmersionCohomologyAddEquiv _ _ q).subsingleton
  exact (actualCohomologyLinearEquivOfIso (cartierInfinitesimalThickeningIso f I D n) q).subsingleton

variable (B : Type u) [CommRing B] (r k : ℕ)
  (e : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) B) ⟶ X)
  (b : (Scheme.Modules.pullback e).obj D.sheaf ≅
    projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ)))

noncomputable def cartierProjectiveInitialQuotientIso
    (a₀ : (unitModule X).quotientIdealPow f I 0 ≅
      (Scheme.Modules.pushforward e).obj (unitModule _)) :
    D.sheaf.quotientIdealPow f I 0 ≅ (Scheme.Modules.pushforward e).obj
      (projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ))) :=
  (cartierInfinitesimalQuotientIso f I D 0).symm ≪≫
    (cartierTwistFunctor D).mapIso a₀ ≪≫
      cartierProjectionFormulaIso D e (unitModule _) ≪≫
        (Scheme.Modules.pushforward e).mapIso
          (rightUnitor ((Scheme.Modules.pullback e).obj D.sheaf) ≪≫ b)

noncomputable def cartierProjectiveLayerIso (n : ℕ)
    (aL : infinitesimalCohomologyLayer f I (unitModule X) n ≅
      (Scheme.Modules.pushforward e).obj
        (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) + 1))) :
    infinitesimalCohomologyLayer f I D.sheaf n ≅
      (Scheme.Modules.pushforward e).obj
        (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) + 1 - k)) :=
  (cartierInfinitesimalLayerIso f I D n).symm ≪≫
    (cartierTwistFunctor D).mapIso aL ≪≫
      cartierProjectionFormulaIso D e _ ≪≫
        (Scheme.Modules.pushforward e).mapIso
          (tensorIso b (Iso.refl _) ≪≫
            sgaLineBundleTensorPowerIso (projectiveSpace.twistingBundle (Fin (r + 1)) B)
              (-(k : ℤ)) ((n : ℤ) + 1) ≪≫
                eqToIso (congrArg (projectiveSpace.twist (Fin (r + 1)) B)
                  (show -(k : ℤ) + ((n : ℤ) + 1) = (n : ℤ) + 1 - k by omega)))

include b in
/-- One restriction isomorphism supplies all Cartier layer identifications.
The unit-layer models and their underlying projective geometry are inputs. -/
theorem proper_cartier_cohomology_vanish_of_projective_unit_layers
    [IsNoetherianRing A] [IsProper f] [D.sheaf.IsCoherent] [IsClosedImmersion e]
    (hI : I ≤ Ideal.jacobson ⊥) (q : ℕ)
    (a₀ : (unitModule X).quotientIdealPow f I 0 ≅
      (Scheme.Modules.pushforward e).obj (unitModule _))
    (aL : ∀ n : ℕ, infinitesimalCohomologyLayer f I (unitModule X) n ≅
      (Scheme.Modules.pushforward e).obj
        (projectiveSpace.twist (Fin (r + 1)) B ((n : ℤ) + 1)))
    (h : q + 1 ≠ r ∨ k ≤ r) :
    Subsingleton (Scheme.Modules.Cohomology D.sheaf (q + 1)) :=
  proper_cohomology_vanish_of_projective_layers I hI f D.sheaf B r q k e
    (cartierProjectiveInitialQuotientIso f I D B r k e b a₀)
    (fun n ↦ cartierProjectiveLayerIso f I D B r k e b n (aL n)) h

end MixedFujita
