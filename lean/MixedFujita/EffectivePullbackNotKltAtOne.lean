/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperNormalBasePrime
public import MixedFujita.KltRoundupExceptional
public import MixedFujita.LogPairOverBasePoint
public import MixedFujita.CrepantBertiniPerturbationDescent

/-!
Adding a full effective base prime pullback to an effective boundary cannot
remain klt over that prime. Construct a prime on the original normal source,
lift it to an actual proper smooth birational model, and use its nonnegative
original crepant boundary coefficient. No computing prime or resolution is input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y]

/-- The full pullback of a positive effective base prime violates the klt bound. -/
theorem effective_base_prime_pullback_not_klt_at_one
    (g : X ⟶ Y) [IsDominant g] [IsProper g]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (H : CartierDivisor Y) (hH : H.IsEffective) (η : CodimensionOnePoint Y)
    (hη : 0 < cartierCoefficient H (η : Y)) :
    ¬ LogPairIsKltOverBasePoint g (η : Y) c f d (D + d • cartierPullback g H) := by
  intro hklt
  obtain ⟨z, hz, hpos⟩ := proper_normal_pullback_exists_positive_prime_over_base_prime
    g hnorm H hH η hη
  obtain ⟨T, hTi, hTo, hTN, hTs, π, hdom, hover, hprop, hπ, cT, r, ξ,
    hinj, hξ, hsnc, hsupp⟩ := exists_proper_snc_model c f d D
  obtain ⟨t, ht, hbij⟩ := proper_birational_exists_normal_prime_lift hnorm π hπ z
  have hcoh : Order.coheight (π (t : T)) = 1 := by simpa only [ht] using z.property
  have hb := crepantBoundary_coefficient_nonneg_over_normal_prime π hπ hnorm hcov
    c f d D heff cT t hcoh
  letI := hnorm (π (t : T))
  letI := normal_codimensionOne_stalk_DVR (⟨π (t : T), hcoh⟩ : CodimensionOnePoint X)
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  letI := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  have hpull := cartierCoefficient_pullback_of_stalkMap_bijective π t hcoh hbij
    (cartierPullback g H)
  rw [ht] at hpull
  have hguard : (η : Y) ∈ closure ({(π ≫ g) (t : T)} : Set Y) := by
    simpa only [Scheme.Hom.comp_apply, ht] using hz
  have hdisc := hklt T π hπ cT (t : T) t.property hguard
  have hbound : cartierCoefficient
      (crepantBoundaryCartier π hπ c f d (D + d • cartierPullback g H) cT etaleCharts_cover)
      (t : T) < (d : ℤ) := by
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
    omega
  rw [crepantBoundaryCartier_add_source, cartierPullback_nsmul,
    cartierCoefficient_add, cartierCoefficient_nsmul, hpull] at hbound
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hm : (1 : ℤ) ≤ cartierCoefficient (cartierPullback g H) (z : X) := by omega
  nlinarith

end MixedFujita
