/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCStrictTransformIdeals
public import MixedFujita.PointBlowupCentreCoefficient
public import Hironaka.Scheme.Snc.TotalTransformSnc

/-! Multiplicity one for actual smooth divisor ideals and for all components of
an SNC total transform. The DVR instances on the blow-up are derived from its
regular stalks and codimension one. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem smoothDivisor_cartierCoefficient
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (I : Y.IdealSheafData) (hI : IsSmoothDivisor I)
    (G : CartierDivisor Y) (hG : G.IsEffective) (hGI : effectiveCartierIdealSheaf G hG = I)
    (t : CodimensionOnePoint Y) [IsDiscreteValuationRing (Y.presheaf.stalk (t : Y))] :
    cartierCoefficient G (t : Y) = if (t : Y) ∈ I.support then 1 else 0 := by
  by_cases ht : (t : Y) ∈ I.support
  · rw [ite_eq_left ht]
    obtain ⟨a, ha, ha2, hIa⟩ := hI.2 _ ht
    apply effectiveCartier_coefficient_of_stalkIdeal_span G hG t a
      (fun h => ha2 (h ▸ Ideal.zero_mem _)) (by rw [hGI]; exact hIa) 1
    exact (localAdicOrder_eq_nat_iff a 1).mpr ⟨by simpa only [pow_one] using ha, ha2⟩
  · rw [ite_eq_right ht]
    exact cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf G hG _
      (by rwa [hGI])

theorem snc_totalTransform_cartierCoefficient
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp]
    (i : (D.totalTransform Z).ι) (G : CartierDivisor Z.blowUp) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (D.totalTransform Z).component i)
    (t : CodimensionOnePoint Z.blowUp) :
    cartierCoefficient G (t : Z.blowUp) =
      if (t : Z.blowUp) ∈ ((D.totalTransform Z).component i).support then 1 else 0 := by
  let := isRegularLocalRing_stalk_blowUp' f D.component Z (hasSncWith_data D Z hZ) (t : Z.blowUp)
  let : IsDiscreteValuationRing (Z.blowUp.presheaf.stalk (t : Z.blowUp)) := inferInstance
  exact smoothDivisor_cartierCoefficient _
    (isSmoothDivisor_totalTransform_component f D Z hD hZ i) G hG hGI t

end MixedFujita
