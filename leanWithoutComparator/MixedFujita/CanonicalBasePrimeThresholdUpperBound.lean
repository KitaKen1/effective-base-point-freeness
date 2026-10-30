/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectivePullbackNotKltAtOne
public import MixedFujita.BasePrimeDiscriminantCoefficients

/-!
The canonical base-prime threshold of an effective klt pair lies in (0,1].
Use an actual normalized local realization and exclude its coefficient-one
perturbation on an internally constructed prime. Consequently the canonical
rational discriminant coefficient lies in [0,1); finite support is still separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Actual open-immersion stalk isomorphisms preserve normality. -/
theorem integrallyClosed_stalk_of_openImmersion {X Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] (j : Z ⟶ X) [IsOpenImmersion j]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (z : Z) :
    IsIntegrallyClosed (Z.presheaf.stalk z) := by
  letI := hnorm (j z)
  exact IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective (j.stalkMap z).hom
    (ConcreteCategory.bijective_of_isIso (j.stalkMap z)))

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y]

variable (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D)

/-- The canonical local threshold cannot exceed one for an effective source boundary. -/
theorem canonicalBasePrimeKltThreshold_le_one
    (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))] :
    canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt ≤ 1 := by
  obtain ⟨a, q₀, ha, hq₀, hvalue, U, hηU, hlocal⟩ :=
    canonicalBasePrimeKltThreshold_realizes g η hnorm hcov c f d hd D heff hklt
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U).ι :=
    ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
  obtain ⟨H, cU, hH, hHη, htests⟩ := hlocal
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ U).toScheme :=
    (g ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : IsNoetherian (g ⁻¹ᵁ U).toScheme := by constructor <;> infer_instance
  haveI : QuasiCompact ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (g ⁻¹ᵁ U).ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι
  let θ : U.toScheme := ⟨(η : Y), hηU⟩
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective U.ι θ
      (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap θ))).trans η.property
  have heffU := logPairBoundaryEffective_open_crepant_pullback (g ⁻¹ᵁ U).ι hj
    hnorm hcov c f d D heff cU
  have hnot := effective_base_prime_pullback_not_klt_at_one (g ∣_ U)
    (integrallyClosed_stalk_of_openImmersion (g ⁻¹ᵁ U).ι hnorm)
    (codimOneChartCovered_open_immersion (g ⁻¹ᵁ U).ι hcov)
    cU _ d hd (cartierPullback (g ⁻¹ᵁ U).ι D) heffU H hH ⟨θ, hθ⟩
    (by rw [hHη]; norm_num)
  have htest := (htests 1 1 (by omega)).1
  simp only [one_mul, mul_one, one_nsmul, Nat.cast_one, div_one] at htest
  exact le_of_not_gt (fun h => hnot (htest.mpr h))

variable (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

/-- Canonical rational discriminant coefficients are nonnegative. -/
theorem basePrimeDiscriminantCoefficients_nonneg (η : CodimensionOnePoint Y) :
    0 ≤ basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η := by
  letI := hnormY (η : Y)
  change 0 ≤ 1 - canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt
  exact sub_nonneg.mpr
    (canonicalBasePrimeKltThreshold_le_one g hnorm hcov c f d hd D heff hklt η)

/-- Every coefficient of the canonical rational family lies in the half-open unit interval. -/
theorem basePrimeDiscriminantCoefficients_mem_Ico (η : CodimensionOnePoint Y) :
    basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η ∈
      Set.Ico (0 : ℚ) 1 :=
  ⟨basePrimeDiscriminantCoefficients_nonneg g hnorm hcov c f d hd D heff hklt hnormY η,
    basePrimeDiscriminantCoefficients_lt_one g hnormY hnorm hcov c f d hd D heff hklt η⟩

end MixedFujita
