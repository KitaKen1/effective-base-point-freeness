/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.OriginalKltSNCStrataTransversality
public import MixedFujita.SNCBasePrimeLogCanonical
public import MixedFujita.LogCanonicalProperCrepantDescent

/-!
From the original klt pair and proper dominant base map, internally construct
one nonempty base open on which adding any actual effective Cartier divisor
with a uniformizer equation at a base prime is lc over that prime. The
proper model, transversality, adapted equation chart, all-test bound and
crepant descent are all internal. This does not yet construct all local
base-open comparisons required for canonical threshold one.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The original klt pair supplies a nonempty base open with actual coefficient-one lc at every base prime. -/
theorem exists_original_klt_base_prime_coefficient_one_logCanonical_open
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : X ⟶ Y) [IsProper g] [IsDominant g]
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧
      ∀ (η : CodimensionOnePoint Y), (η : Y) ∈ V →
      ∀ (H : CartierDivisor Y) (_ : H.IsEffective) (fH : Y.functionFieldˣ),
        H.IsLocalEquationAt (η : Y) fH →
      ∀ a : Y.presheaf.stalk (η : Y),
        algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField a = (fH : Y.functionField) →
        Irreducible a →
        LogPairIsLogCanonicalOverBasePoint g (η : Y) c f d (D + d • cartierPullback g H) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, π, hdom, hover, hprop, hπ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hb, V, hηV, hne, hV, htrans⟩ :=
    exists_original_klt_snc_model_with_uniformizer_transverse_strata_open g hnormY c f d D hklt
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  haveI : IsSeparated (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  haveI : QuasiCompact (T ↘ Spec (CommRingCat.of K)) := inferInstance
  refine ⟨V, hηV, ?_⟩
  intro η hη H hH fH hfH a ha hairred
  let B := crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover
  let fT := crepantPullbackFormUnit π hπ c f cT
  have hlc := snc_base_prime_pullback_logCanonical_overBasePoint (π ≫ g) cT fT d hd B
    ξ hinj hcoh hsnc hsupp (fun i => (hb i).le) V htrans η hη H hH fH hfH a ha hairred
  have hpair : d • (smoothCanonicalDivisor cT + principalCartierDivisor T fT) +
      (B + d • cartierPullback (π ≫ g) H) = cartierPullback π (D + d • cartierPullback g H) := by
    rw [← add_assoc, crepantBoundaryCartier_smooth_recombine, cartierPullback_add,
      cartierPullback_nsmul, cartierPullback_comp]
  rw [hpair] at hlc
  exact logPairIsLogCanonicalOverBasePoint_of_proper_crepant_pullback π hπ g (η : Y)
    c f d hd (D + d • cartierPullback g H) cT hlc

end MixedFujita
