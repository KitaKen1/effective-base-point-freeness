/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalPrimeLifts
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
A prime divisor on an integral birational model cannot have a codimension-zero centre. If the
closure of its centre contains a specified codimension-one point, the centre is that point.
This removes the apparent choice of centres in realization at a base prime, in any dimension.
Neither properness nor smoothness is needed for these centre statements.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {Y U : Scheme.{u}} [IsIntegral Y] [IsIntegral U]
  (σ : U ⟶ Y) [IsDominant σ]
  (hσ : Function.Bijective (dominantFunctionFieldMap σ).hom)

include hσ

/-- A birational prime divisor cannot map to a codimension-zero point: its stalk would then
be isomorphic to a field, contradicting its coheight. -/
theorem one_le_coheight_birational_prime_image (e : CodimensionOnePoint U) :
    1 ≤ Order.coheight (σ (e : U)) := by
  apply Order.one_le_iff_pos.mpr
  by_contra hnot
  have hzero : Order.coheight (σ (e : U)) = 0 := le_antisymm (not_lt.mp hnot) bot_le
  have hdim : Ring.KrullDimLE 0 (Y.presheaf.stalk (σ (e : U))) :=
    krullDimLE_of_coheight_le hzero.le
  have hfield : IsField (Y.presheaf.stalk (σ (e : U))) :=
    Ring.isField_iff_maximal_bot.mpr (Ring.krullDimLE_zero_iff.mp hdim ⊥ Ideal.isPrime_bot)
  let := hfield.toField
  have hb := stalkMap_bijective_of_birational_valuation_stalk σ hσ (e : U)
  have hc := coheight_eq_of_stalkMap_bijective σ (e : U) hb
  rw [e.property, hzero] at hc
  exact one_ne_zero hc

/-- A prime centre specializing to a codimension-one base point equals that point. The
specialization condition does not leave a family of possible prime centres in this case. -/
theorem birational_prime_image_eq_of_mem_closure {x : Y} (hx : Order.coheight x = 1)
    (e : CodimensionOnePoint U) (hcentre : x ∈ closure ({σ (e : U)} : Set Y)) :
    σ (e : U) = x := by
  let : PartialOrder Y := specializationOrder Y
  have hle : x ≤ σ (e : U) := Scheme.le_iff_specializes.mpr
    (specializes_iff_mem_closure.mpr hcentre)
  have hcod : Order.coheight (σ (e : U)) = 1 := le_antisymm
    ((Order.coheight_anti hle).trans hx.le) (one_le_coheight_birational_prime_image σ hσ e)
  by_contra hne
  have hlt : x < σ (e : U) := lt_of_le_of_ne hle (Ne.symm hne)
  have hstrict := Order.coheight_strictAnti hlt (by rw [hcod]; exact ENat.natCast_lt_top 1)
  rw [hx, hcod] at hstrict
  exact lt_irrefl _ hstrict

end MixedFujita
