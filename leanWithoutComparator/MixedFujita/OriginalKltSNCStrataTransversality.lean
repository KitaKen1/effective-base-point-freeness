/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.OriginalKltSNCStrataOpen
public import MixedFujita.SNCStrataUniformizerTransversality
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.DominantOpenBaseRestriction

/-!
From the original klt Cartier presentation over a normal locally finite type
characteristic-zero base, construct the same actual proper SNC model, strict
boundary coefficients and nonempty source/base opens. Every base-prime
uniformizer is transverse to every actual closed SNC stratum on this open.
No model, comparison or transversality certificate is input. Coefficient-one
lc and finite discriminant support still require the joint-boundary argument.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The original klt pair internally supplies a proper SNC model and a uniformly transverse base open. -/
theorem exists_original_klt_snc_model_with_uniformizer_transverse_strata_open
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : X ⟶ Y) [IsProper g] [IsDominant g]
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (hklt : LogPairIsKlt c f d D) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (π : T ⟶ X) (_ : IsDominant π) (_ : π.IsOver (Spec (CommRingCat.of K))) (_ : IsProper π)
      (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover) (t : T) = 0) ∧
      (∀ i, cartierCoefficient (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover)
        (ξ i) < (d : ℤ)) ∧
      ∃ V : Y.Opens, genericPoint Y ∈ V ∧ Nonempty ((π ≫ g) ⁻¹ᵁ V) ∧
        (∀ s : Finset (ULift.{u} (Fin r)),
          Smooth (((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) s).subschemeι ≫ (π ≫ g)) ∣_ V)) ∧
        SNCStrataUniformizerTransverseOn (π ≫ g) (sncDivisorFamilyOfPoints ξ) V := by
  obtain ⟨T, hTi, hTo, hTN, hTs, π, hdom, hover, hprop, hπ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hb, V, hηV, hne, hV⟩ :=
    exists_original_klt_snc_model_with_common_smooth_strata_open g c f d D hklt
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  exact ⟨T, hTi, hTo, hTN, hTs, π, hdom, hover, hprop, hπ, cT, r, ξ, hinj, hcoh,
    hsnc, hsupp, hb, V, hηV, hne, hV,
    sncStrataUniformizerTransverseOn_of_smooth_restrictions (K := K) (π ≫ g)
      (sncDivisorFamilyOfPoints ξ) (sncDivisorFamilyOfPoints_isSnc ξ hsnc) hnormY V hV⟩

end MixedFujita
