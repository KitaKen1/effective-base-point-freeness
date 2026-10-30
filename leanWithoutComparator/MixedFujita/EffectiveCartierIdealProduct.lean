/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InducedEffectiveCartierDivisor
public import MixedFujita.PrincipalizedIdealCoefficients

/-! Products of actual ideal sheaves identify sums of effective Cartier divisors.
This comparison retains scheme multiplicities and needs no normality assumption. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

theorem effectiveCartierIdealSheaf_add (D E : CartierDivisor X)
    (hD : D.IsEffective) (hE : E.IsEffective) :
    effectiveCartierIdealSheaf (D + E) (hD.add hE) =
      effectiveCartierIdealSheaf D hD * effectiveCartierIdealSheaf E hE := by
  apply Scheme.IdealSheafData.ext_stalkIdeal
  intro x
  obtain ⟨f, hf, a, ha⟩ := CartierDivisor.isEffective_iff_exists.mp hD x
  obtain ⟨g, hg, b, hb⟩ := CartierDivisor.isEffective_iff_exists.mp hE x
  rw [Scheme.IdealSheafData.stalkIdeal_mul,
    effectiveCartier_stalkIdeal_eq_span_of_localEquation D hD x f hf a ha,
    effectiveCartier_stalkIdeal_eq_span_of_localEquation E hE x g hg b hb,
    effectiveCartier_stalkIdeal_eq_span_of_localEquation (D + E) (hD.add hE)
      x (f * g) (hf.mul hg) (a * b) (by rw [map_mul, ha, hb]; rfl),
    Ideal.span_singleton_mul_span_singleton]

omit [IsLocallyNoetherian X] in
theorem cartierPullback_eq_add_of_ideal_product
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : Y ⟶ X) [IsDominant f] (D : CartierDivisor X) (hD : D.IsEffective)
    (G E : CartierDivisor Y) (hG : G.IsEffective) (hE : E.IsEffective)
    (hI : (effectiveCartierIdealSheaf D hD).comap f =
      effectiveCartierIdealSheaf G hG * effectiveCartierIdealSheaf E hE) :
    cartierPullback f D = G + E := by
  apply effectiveCartier_eq_of_idealSheaf_eq _ _ (cartierPullback_isEffective f D hD)
    (hG.add hE)
  rw [effectiveCartierIdealSheaf_cartierPullback, effectiveCartierIdealSheaf_add]
  exact hI

end MixedFujita
