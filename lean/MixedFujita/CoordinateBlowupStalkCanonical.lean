/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateBlowupRelativeCanonical
public import MixedFujita.RelativeCanonicalStalkOrder
public import MixedFujita.LocalBirationalOrders

/-! The coordinate-center relative canonical coefficient from actual formally
etale stalk coordinates. The comparison to an arbitrary scheme chart is a unit;
o new scheme chart is needed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
universe u

theorem coordinateBlowup_etaleDVR_jacobian_order {K R S : Type*} [Field K]
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    [IsDomain S] [IsDiscreteValuationRing S] {n : ℕ}
    (β : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y z : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hz : z.toRingHom.FormallyEtale)
    (s : Finset (Fin n)) (k : Fin n) (hk : ¬ IsUnit (y (MvPolynomial.X k)))
    (hcoord : ∀ i, β (x (MvPolynomial.X i)) =
      if i = k then y (MvPolynomial.X k) else if i ∈ s then y (MvPolynomial.X i) * y (MvPolynomial.X k)
      else y (MvPolynomial.X i)) :
    localAdicOrder S (etaleRelativeJacobian β x z hz).det = ((s.erase k).card : ℕ) := by
  rw [etaleRelativeJacobian_det_change_target β x y z hy hz,
    coordinateBlowup_etaleRelativeJacobian_det β x y hy s k hcoord,
    dvr_localAdicOrder_eq_addVal, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer (etaleDVR_coordinate_irreducible y hy k hk),
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (Module.Basis.isUnit_det _ _)]
  simp


variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {n : ℕ}
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable [IsLocallyNoetherian T]

theorem coordinateBlowup_stalk_relativeCanonical_coefficient
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (c : EtaleChart K X n) (hc : ρ (t : T) ∈ c.U)
    (τ : MvPolynomial (Fin n) K →ₐ[K] T.presheaf.stalk (t : T))
    (hτ : τ.toRingHom.FormallyEtale) (s : Finset (Fin n)) (k : Fin n) (hk : ¬ IsUnit (τ (MvPolynomial.X k)))
    (hcoord : ∀ i, schemeStalkMapAlgHom (K := K) ρ (t : T)
      (etaleChartStalkCoords c (ρ (t : T)) hc (MvPolynomial.X i)) =
        if i = k then τ (MvPolynomial.X k) else if i ∈ s then τ (MvPolynomial.X i) * τ (MvPolynomial.X k)
        else τ (MvPolynomial.X i)) :
    cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR) (t : T) = ((s.erase k).card : ℤ) := by
  obtain ⟨c', hc'⟩ := Opens.mem_iSup.mp (hT.symm ▸ Opens.mem_top (t : T))
  let d := (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ (t : T))
    (etaleChartStalkCoords c (ρ (t : T)) hc) (etaleChartStalkCoords c' (t : T) hc')
    (etaleChartStalkCoords_formallyEtale c' (t : T) hc')).det
  have hd : d ≠ 0 := by
    intro hd
    have hu := (isUnit_chartRelativeJacobianDet ρ c₀ c'₀ hR c c').ne_zero
    rw [chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc'] at hu
    exact hu (by change stalkFunctionFieldAlgHom (K := K) (t : T) d = 0; rw [hd, map_zero])
  have ho : localAdicOrder (T.presheaf.stalk (t : T)) d = ((s.erase k).card : ℕ) :=
    coordinateBlowup_etaleDVR_jacobian_order _ _ τ _ hτ _ s k hk hcoord
  rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt ρ
    c₀ hX c'₀ hT hR (t : T) c hc c' hc'), IsUnit.unit_spec,
    chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc']
  change T.ord (algebraMap (T.presheaf.stalk (t : T)) T.functionField d) (t : T) = ((s.erase k).card : ℤ)
  exact
    scheme_ord_regular_eq_localAdicOrder_nat t d hd (s.erase k).card ho

theorem relativeCanonical_coefficient_zero_of_stalkMap_bijective
    (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (c'₀ : EtaleChart K T n) (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))]
    (ht : Function.Bijective (ρ.stalkMap (t : T))) :
    cartierCoefficient (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR) (t : T) = 0 := by
  obtain ⟨c, hc⟩ := Opens.mem_iSup.mp (hX.symm ▸ Opens.mem_top (ρ (t : T)))
  obtain ⟨c', hc'⟩ := Opens.mem_iSup.mp (hT.symm ▸ Opens.mem_top (t : T))
  apply relativeCanonical_coefficient_of_stalk_jacobian_order ρ c₀ hX c'₀ hT hR t c hc c' hc' 0
  exact Ring.ord_of_isUnit (chartRelativeJacobianDet_stalk_isUnit_of_bijective ρ (t : T) ht c hc c' hc')

end MixedFujita
