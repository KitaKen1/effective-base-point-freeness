/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupStalkCanonical

/-! Compute the actual relative canonical Cartier coefficient from the
intrinsic DVR order of the actual stalk Jacobian. The local chart
Jacobian is nonzero because its image is the nonzero function-field
Jacobian. No coordinate-specific coefficient formula is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {n : ℕ}
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

theorem relativeCanonical_stalk_jacobian_ne_zero
    (c₀ : EtaleChart K X n) (cT₀ : EtaleChart K T n)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ cT₀)) (t : T)
    (c : EtaleChart K X n) (hc : ρ t ∈ c.U) (cT : EtaleChart K T n) (hcT : t ∈ cT.U) :
    (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ t)
      (etaleChartStalkCoords c (ρ t) hc) (etaleChartStalkCoords cT t hcT)
      (etaleChartStalkCoords_formallyEtale cT t hcT)).det ≠ 0 := by
  intro hz
  have hu := (isUnit_chartRelativeJacobianDet ρ c₀ cT₀ hR c cT).ne_zero
  rw [chartRelativeJacobianDet_eq_stalk ρ t c hc cT hcT] at hu
  exact hu (by rw [hz, map_zero])

theorem relativeCanonical_coefficient_of_stalk_jacobian_order [IsLocallyNoetherian T]
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (cT₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ cT₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (cT : EtaleChart K T n) (hcT : (t : T) ∈ cT.U) (m : ℕ)
    (hm : Ring.ord (T.presheaf.stalk (t : T))
      (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ (t : T))
        (etaleChartStalkCoords c (ρ (t : T)) hc) (etaleChartStalkCoords cT (t : T) hcT)
        (etaleChartStalkCoords_formallyEtale cT (t : T) hcT)).det = (m : ℕ∞)) :
    cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX cT₀ hT hR) (t : T) = (m : ℤ) := by
  let d := (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ (t : T))
    (etaleChartStalkCoords c (ρ (t : T)) hc) (etaleChartStalkCoords cT (t : T) hcT)
    (etaleChartStalkCoords_formallyEtale cT (t : T) hcT)).det
  have hd : d ≠ 0 := relativeCanonical_stalk_jacobian_ne_zero ρ c₀ cT₀ hR (t : T) c hc cT hcT
  have hdorder : localAdicOrder (T.presheaf.stalk (t : T)) d = (m : ℕ∞) :=
    (dvr_localAdicOrder_eq_ringOrd d).trans hm
  rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt ρ
    c₀ hX cT₀ hT hR (t : T) c hc cT hcT), IsUnit.unit_spec,
    chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc cT hcT]
  change T.ord (algebraMap (T.presheaf.stalk (t : T)) T.functionField d) (t : T) = (m : ℤ)
  exact scheme_ord_regular_eq_localAdicOrder_nat t d hd m hdorder

end MixedFujita
