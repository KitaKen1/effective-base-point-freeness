/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SpecializationStalkEmbedding
public import MixedFujita.SNCStrictTransformIdeals
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
public import Hironaka.Scheme.Smooth.SubschemeStalk

/-! On an integral center, containment at one stalk detects global containment.
This supplies the uniform incidence needed by the actual SNC total-transform formula. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme.IdealSheafData
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem integral_idealSheaf_eq_bot_of_stalkIdeal_eq_bot
    {Y : Scheme.{u}} [IsIntegral Y] (I : Y.IdealSheafData) (y : Y)
    (hy : I.stalkIdeal y = ⊥) : I = ⊥ := by
  have hg : I.stalkIdeal (genericPoint Y) = ⊥ :=
    I.stalkIdeal_eq_bot_of_specializes ((genericPoint_spec Y).specializes trivial) hy
  apply ext_stalkIdeal
  intro z
  rw [stalkIdeal_bot]
  have hz := (genericPoint_spec Y).specializes (Set.mem_univ z)
  rw [I.stalkIdeal_specializes hz] at hg
  exact (Ideal.map_eq_bot_iff_of_injective (integral_stalkSpecializes_injective hz)).mp hg

theorem integralSubscheme_stalkIdeal_le_iff
    {X : Scheme.{u}} (D Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    (x : X) (hx : x ∈ Z.support) :
    D.stalkIdeal x ≤ Z.stalkIdeal x ↔ D ≤ Z := by
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := Z.exists_subschemeι_eq hx
    have hbot : (D.comap Z.subschemeι).stalkIdeal z = ⊥ := by
      rw [stalkIdeal_comap, Ideal.map_eq_bot_iff_le_ker, Z.ker_stalkMap_subschemeι]
      exact h
    have heq := integral_idealSheaf_eq_bot_of_stalkIdeal_eq_bot _ z hbot
    have hle := le_map_comap D Z.subschemeι
    rw [heq, map_bot, Z.ker_subschemeι] at hle
    exact hle
  · exact fun h => stalkIdeal_mono h x

theorem snc_integralCentre_totalTransform
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    (hD : D.IsSnc) (hZ : D.HasSncWith Z) (i : D.ι) :
    (D.component i).comap Z.blowUpπ = (D.component i).strictTransform Z *
      (if D.component i ≤ Z then Z.exceptionalDivisor else ⊤) :=
  snc_strictTransform_totalTransform f D Z hD hZ i (D.component i ≤ Z)
    (fun x hx => integralSubscheme_stalkIdeal_le_iff _ Z x hx)

end MixedFujita
