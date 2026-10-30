/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalBasePrimeThresholdLocalTests
public import MixedFujita.CanonicalBasePrimeThresholdUpperBound

/-! One actual normalized local lc test at coefficient one, together with
the proved upper bound, forces the canonical base-prime threshold to one. -/

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
  (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D)

/-- A single actual coefficient-one local lc test determines the canonical endpoint. -/
theorem canonicalBasePrimeKltThreshold_eq_one_of_local_logCanonical
    (U : Y.Opens) (hηU : (η : Y) ∈ U) :
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
    letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
      ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    letI : IsDominant (g ⁻¹ᵁ U).ι :=
      ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
    ∀ (H : CartierDivisor U.toScheme) (_ : H.IsEffective)
      (_ : cartierCoefficient H (⟨(η : Y), hηU⟩ : U.toScheme) = 1)
      (cU : EtaleChart K (g ⁻¹ᵁ U).toScheme n),
      let fU := crepantPullbackFormUnit (g ⁻¹ᵁ U).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι) c f cU
      let DU := cartierPullback (g ⁻¹ᵁ U).ι D
      LogPairIsLogCanonicalOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme)
        cU fU d (DU + d • cartierPullback (g ∣_ U) H) →
        canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = 1 := by
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U).ι :=
    ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
  intro H hH hHη cU
  dsimp only
  intro hlc
  apply le_antisymm (canonicalBasePrimeKltThreshold_le_one g hnorm hcov c f d hd D heff hklt η)
  have htest := (canonicalBasePrimeKltThreshold_local_tests
    g η hnorm hcov c f d hd D heff hklt U hηU H hH hHη cU 1 1 (by omega)).2
  have htest' : LogPairIsLogCanonicalOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme)
      cU (crepantPullbackFormUnit (g ⁻¹ᵁ U).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι) c f cU) d
      (cartierPullback (g ⁻¹ᵁ U).ι D + d • cartierPullback (g ∣_ U) H) ↔
      (1 : ℚ) ≤ canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt := by
    simpa only [Nat.one_mul, one_nsmul, mul_one, Nat.cast_one, div_one] using htest
  exact htest'.mp hlc

end MixedFujita
