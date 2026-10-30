/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateBlowupStalkCoordinates
public import MixedFujita.CoordinateBlowupStalkCanonical
public import MixedFujita.SNCSmoothDivisorCoefficients
public import MixedFujita.NormalCartierCoefficientExt
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.HironakaPrincipalizingRound
public import Hironaka.Scheme.Smooth.BlowUpSmooth
public import Hironaka.Scheme.Smooth.ExceptionalBundle
public import Mathlib.Data.Fintype.Fin

/-! The actual relative canonical divisor of an SNC blow-up with fixed smooth
relative dimensions is `(r - 1) E`. Adapted coordinates and their actual stalk
equations are constructed at every codimension-one point over the center.
Outside the center the stalk map is an isomorphism. Equality of Cartier divisors
then follows from their coefficients on the regular blow-up. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
universe u
variable {K : Type u} [Field K] {n r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of K))] {Z : X.IdealSheafData} {x : X}
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

set_option maxHeartbeats 800000 in
theorem coordinateBlowup_matched_relativeCanonical_coefficient
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp] [IsDominant Z.blowUpπ]
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n r Z x) (hrn : r ≤ n) :
    let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
    let : Z.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
    ∀ (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
      (c'₀ : EtaleChart K Z.blowUp n) (hT : iSup (fun c : EtaleChart K Z.blowUp n => c.U) = ⊤)
      (hR : IsUnit (chartRelativeJacobianDet Z.blowUpπ c₀ c'₀))
      (t : CodimensionOnePoint Z.blowUp) [IsDiscreteValuationRing (Z.blowUp.presheaf.stalk (t : Z.blowUp))]
      (_ht : Z.blowUpπ (t : Z.blowUp) ∈ E.U.1) (_htZ : Z.blowUpπ (t : Z.blowUp) ∈ Z.support),
      cartierCoefficient (relativeCanonicalDivisor n Z.blowUpπ c₀ hX c'₀ hT hR) (t : Z.blowUp) =
        ((r - 1 : ℕ) : ℤ) := by
  let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
  let : Z.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
  dsimp only
  intro c₀ hX c'₀ hT hR t _ ht htZ
  obtain ⟨k, hk, τ, hτ, hnonunit, hcoord⟩ :=
    etaleCoordinateBlowup_matched_stalk_coordinates E (t : Z.blowUp) ht htZ
  let c := etaleChartOfToAffineSpace E.U ⟨⟨x, E.mem⟩⟩ E.v E.etale
  have hc : Z.blowUpπ (t : Z.blowUp) ∈ c.U := ht
  let s := Finset.univ.filter (fun i : Fin n => i.val < r)
  have hcard : (s.erase k).card = r - 1 := by
    rw [Finset.card_erase_of_mem (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hk)]
    change (Finset.univ.filter (fun i : Fin n => i.val < r)).card - 1 = r - 1
    rw [Fin.card_filter_val_lt, Nat.min_eq_right hrn]
  rw [← hcard]
  apply coordinateBlowup_stalk_relativeCanonical_coefficient Z.blowUpπ
    c₀ hX c'₀ hT hR t c hc τ hτ s k hnonunit
  intro i
  change Z.blowUpπ.stalkMap (t : Z.blowUp) (X.presheaf.germ E.U.1 _ hc
    (c.coords (MvPolynomial.X i))) = _
  rw [etaleChartOfToAffineSpace_coords]
  simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hcoord i

set_option maxHeartbeats 1000000 in
theorem snc_blowUp_relativeCanonical_eq_nsmul
    [PerfectField K] [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hD : D.IsSnc) (hZ : D.HasSncWith Z)
    [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ (X ↘ Spec (.of K)))] (hrn : r ≤ n)
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp] [IsDominant Z.blowUpπ]
    (E : CartierDivisor Z.blowUp) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = Z.exceptionalDivisor) :
    let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
    let : Z.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
    ∀ (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
      (c'₀ : EtaleChart K Z.blowUp n) (hT : iSup (fun c : EtaleChart K Z.blowUp n => c.U) = ⊤)
      (hR : IsUnit (chartRelativeJacobianDet Z.blowUpπ c₀ c'₀)),
      relativeCanonicalDivisor n Z.blowUpπ c₀ hX c'₀ hT hR = (r - 1) • E := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
  let : Z.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
  dsimp only
  intro c₀ hX c'₀ hT hR
  let : SmoothOfRelativeDimension n (Z.blowUp ↘ Spec (.of K)) :=
    smoothOfRelativeDimension_blowUpπ_comp (X ↘ Spec (.of K)) n r Z hrn
  let : Smooth (Z.blowUp ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  apply cartierDivisor_eq_of_forall_coefficient_eq (smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n))
  intro t
  let := isRegularLocalRing_stalk_blowUp' (X ↘ Spec (.of K)) D.component Z
    (hasSncWith_data D Z hZ) (t : Z.blowUp)
  let : IsDiscreteValuationRing (Z.blowUp.presheaf.stalk (t : Z.blowUp)) := inferInstance
  have hEc := snc_totalTransform_cartierCoefficient (X ↘ Spec (.of K)) D Z hD hZ
    (toLex (Sum.inr PUnit.unit)) E hE hEI t
  change cartierCoefficient E (t : Z.blowUp) =
    if (t : Z.blowUp) ∈ Z.exceptionalDivisor.support then 1 else 0 at hEc
  have hEs : (t : Z.blowUp) ∈ Z.exceptionalDivisor.support ↔ Z.blowUpπ (t : Z.blowUp) ∈ Z.support :=
    mem_support_comap_iff_apply Z Z.blowUpπ (t : Z.blowUp)
  rw [cartierCoefficient_nsmul, hEc]
  by_cases htZ : Z.blowUpπ (t : Z.blowUp) ∈ Z.support
  · rw [ite_eq_left (hEs.mpr htZ), mul_one]
    have hz : Z.blowUpπ (t : Z.blowUp) ∈ Set.range Z.subschemeι := by
      rwa [Z.range_subschemeι]
    obtain ⟨z, hz⟩ := hz
    obtain ⟨x, hx⟩ := exists_adaptedChart_mem (X ↘ Spec (.of K)) n r Z hrn z
    exact coordinateBlowup_matched_relativeCanonical_coefficient
      (adaptedChart (X ↘ Spec (.of K)) n r Z hrn x) hrn c₀ hX c'₀ hT hR t (hz ▸ hx) htZ
  · rw [ite_eq_right (fun h => htZ (hEs.mp h)), mul_zero]
    let := blowUp_isIso_stalkMap_of_notMem_support Z (t : Z.blowUp) htZ
    exact relativeCanonical_coefficient_zero_of_stalkMap_bijective Z.blowUpπ
      c₀ hX c'₀ hT hR t (ConcreteCategory.bijective_of_isIso (Z.blowUpπ.stalkMap (t : Z.blowUp)))

end MixedFujita
