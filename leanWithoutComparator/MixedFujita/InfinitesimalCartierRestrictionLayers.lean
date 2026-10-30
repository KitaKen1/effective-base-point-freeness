/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierCutNaturalInclusion
public import MixedFujita.CartierCutQuotientTransport
public import MixedFujita.EffectiveCartierCutSemiampleness
public import MixedFujita.CartierInfinitesimalVanishing

/-! Actual infinitesimal layers are restrictions of negative Cartier powers.
One degree-one restriction on the actual exceptional scheme supplies all
projective layer models and the resulting proper vanishing criterion. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open CohomologyAux
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{u}} [IsIntegral X]

noncomputable def cartierIdealPowerCutIso (E : CartierDivisor X)
    (hE : E.IsEffective) (n : ℕ) :
    cokernel (cartierIdealPowerInclusion E hE n) ≅
      (cartierCutShortComplex (-(n • E)) E hE).X₃ :=
  cokernel.mapIso _ _
      (eqToIso (congrArg CartierDivisor.sheaf (negativeCartierMultiple_succ E n)))
      (Iso.refl _) (by
        rw [Iso.refl_hom, Category.comp_id, cartierCutShortComplex_first_map_eq_inclusion]
        rfl) ≪≫
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
      (cartierCutShortComplex_shortExact (-(n • E)) E hE).gIsCokernel

variable {A : CommRingCat.{u}} [IsNoetherianRing A]
  (f : X ⟶ Spec A) (I : Ideal A) (E : CartierDivisor X) (hE : E.IsEffective)
  (hJ : effectiveCartierIdealSheaf E hE = infinitesimalBaseIdealSheaf f I)

noncomputable def infinitesimalLayerCartierRestrictionIso (n : ℕ) :
    infinitesimalCohomologyLayer f I (unitModule X) n ≅
      (Scheme.Modules.pushforward (effectiveCartierIdealSheaf E hE).subschemeι).obj
        ((Scheme.Modules.pullback (effectiveCartierIdealSheaf E hE).subschemeι).obj
          (-((n + 1) • E)).sheaf) :=
  infinitesimalLayerCartierCokernelIso f I E hE hJ n ≪≫ cartierIdealPowerCutIso E hE (n + 1)

noncomputable def infinitesimalInitialCartierQuotientIso :
    (unitModule X).quotientIdealPow f I 0 ≅
      (Scheme.Modules.pushforward (effectiveCartierIdealSheaf E hE).subschemeι).obj
        (unitModule (effectiveCartierIdealSheaf E hE).subscheme) :=
  infinitesimalQuotientIdealSubschemeIso f I 0 ≪≫
    eqToIso (congrArg (fun J : X.IdealSheafData =>
      (Scheme.Modules.pushforward J.subschemeι).obj (unitModule J.subscheme))
      ((pow_one (infinitesimalBaseIdealSheaf f I)).trans hJ.symm))

variable {Y : Scheme.{u}} (e : (effectiveCartierIdealSheaf E hE).subscheme ≅ Y)
  (p : Y ⟶ X) (hp : e.inv ≫ (effectiveCartierIdealSheaf E hE).subschemeι = p)
  (L : Y.LineBundle) (a : (Scheme.Modules.pullback p).obj (-E).sheaf ≅ L.toModules 1)

noncomputable def infinitesimalLayerLineBundlePowerIso (n : ℕ) :
    infinitesimalCohomologyLayer f I (unitModule X) n ≅
      (Scheme.Modules.pushforward p).obj (L.toModules ((n : ℤ) + 1)) :=
  infinitesimalLayerCartierCokernelIso f I E hE hJ n ≪≫
    cartierIdealPowerCutIso E hE (n + 1) ≪≫
      cartierCutQuotientPushforwardIsoOfSubschemeIso (-((n + 1) • E)) E hE e p hp ≪≫
        (Scheme.Modules.pushforward p).mapIso
          ((Scheme.Modules.pullback p).mapIso
            (eqToIso (congrArg CartierDivisor.sheaf (smul_neg (n + 1) E).symm)) ≪≫
              cartierPulledSGANatPowerIso p (-E) L a (n + 1) ≪≫
                eqToIso (congrArg L.toModules (Nat.cast_add_one n)))

include hJ in
/-- A projective exceptional scheme, its degree-one conormal restriction,
and one Cartier restriction suffice; no degreewise layer identifications are assumed. -/
theorem proper_cartier_cohomology_vanish_of_projective_exceptional_divisor
    [IsProper f] (D : CartierDivisor X) [D.sheaf.IsCoherent]
    (B : Type u) [CommRing B] (r k : ℕ)
    (eP : (effectiveCartierIdealSheaf E hE).subscheme ≅
      Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) B))
    (pP : Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) B) ⟶ X)
    [IsClosedImmersion pP]
    (hpP : eP.inv ≫ (effectiveCartierIdealSheaf E hE).subschemeι = pP)
    (aP : (Scheme.Modules.pullback pP).obj (-E).sheaf ≅
      projectiveSpace.twist (Fin (r + 1)) B 1)
    (bP : (Scheme.Modules.pullback pP).obj D.sheaf ≅
      projectiveSpace.twist (Fin (r + 1)) B (-(k : ℤ)))
    (hI : I ≤ Ideal.jacobson ⊥) (q : ℕ) (h : q + 1 ≠ r ∨ k ≤ r) :
    Subsingleton (Scheme.Modules.Cohomology D.sheaf (q + 1)) :=
  proper_cartier_cohomology_vanish_of_projective_unit_layers f I D B r k pP bP hI q
    (infinitesimalInitialCartierQuotientIso f I E hE hJ ≪≫
      idealSubschemePushforwardUnitIsoOfIso (effectiveCartierIdealSheaf E hE) eP pP hpP)
    (fun n => infinitesimalLayerLineBundlePowerIso f I E hE hJ eP pP hpP
      (projectiveSpace.twistingBundle (Fin (r + 1)) B) aP n) h

end MixedFujita
