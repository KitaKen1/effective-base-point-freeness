/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModifiedBaseThresholdOneOpen
public import MixedFujita.BasePrimeDiscriminantWeilDivisor

/-!
The actual canonical rational discriminant Weil divisor on a compatible modified base,
constructed from the original effective klt pair and the proved finite support. Its
coefficients may be negative. It agrees with the original discriminant at corresponding
base primes on the isomorphism neighbourhood and is unique with its canonical coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T Y B : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral Y] [IsIntegral B]
  [IsNoetherian X] [IsNoetherian T] [IsLocallyNoetherian Y] [IsNoetherian B]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of K))]
  [IsSeparated (T ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (g : X ⟶ Y) [IsDominant g] [IsProper g] (ρ : B ⟶ Y) [IsDominant ρ]
  (q : T ⟶ B) [IsDominant q] [IsProper q] (hsquare : q ≫ ρ = π ≫ g)
  (W : Y.Opens) [IsIso (ρ ∣_ W)] (hW : genericPoint Y ∈ W)
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n)

include hsquare hW heff hnormY hnormX

/-- Construct the actual rational Weil divisor of the crepant pair on the modified base. -/
noncomputable def modifiedBaseCanonicalSubKltDiscriminantWeilDivisor : CodimensionOnePoint B →₀ ℚ := by
  let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
  exact Finsupp.ofSupportFinite
    (subKltBasePrimeDiscriminantCoefficients q hnormB cT (crepantPullbackFormUnit π hπ c f cT)
      d hd (cartierPullback π D) hkltT)
    (modified_base_subKlt_discriminant_coefficients_finite_support π hπ g ρ q hsquare W hW hnormY hnormX hnormB c f d hd D heff hklt cT)

/-- Every coefficient is the actual one-minus-canonical-threshold coefficient of the new pair. -/
theorem modifiedBaseCanonicalSubKltDiscriminantWeilDivisor_apply (β : CodimensionOnePoint B) :
    let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
    modifiedBaseCanonicalSubKltDiscriminantWeilDivisor π hπ g ρ q hsquare W hW hnormY hnormX hnormB c f d hd D heff hklt cT β =
      subKltBasePrimeDiscriminantCoefficients q hnormB cT (crepantPullbackFormUnit π hπ c f cT)
        d hd (cartierPullback π D) hkltT β := by
  rfl

/-- The actual modified-base Weil coefficients are strictly below one, without a lower-bound claim. -/
theorem modifiedBaseCanonicalSubKltDiscriminantWeilDivisor_lt_one (β : CodimensionOnePoint B) :
    modifiedBaseCanonicalSubKltDiscriminantWeilDivisor π hπ g ρ q hsquare W hW hnormY hnormX hnormB c f d hd D heff hklt cT β < 1 := by
  let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
  exact subKltBasePrimeDiscriminantCoefficients_lt_one q hnormB cT
    (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT β

/-- On corresponding primes the new actual Weil divisor agrees with the original one. -/
theorem modifiedBaseCanonicalSubKltDiscriminantWeilDivisor_eq_original
    (η : CodimensionOnePoint Y) (β : CodimensionOnePoint B)
    (hβ : ρ (β : B) = (η : Y)) (hηW : (η : Y) ∈ W) :
    let hcov := normal_codimOneChartCovered (K := K) (etaleChart_topologicalKrullDim c) hnormX
    modifiedBaseCanonicalSubKltDiscriminantWeilDivisor π hπ g ρ q hsquare W hW hnormY hnormX hnormB c f d hd D heff hklt cT β =
      canonicalBasePrimeDiscriminantWeilDivisor g hnormY hnormX hcov c f d hd D heff hklt η := by
  dsimp only
  let hcov := normal_codimOneChartCovered (K := K) (etaleChart_topologicalKrullDim c) hnormX
  letI := hnormY (η : Y)
  letI := hnormB (β : B)
  have heq := subKltBasePrimeDiscriminantCoefficients_eq_of_compatible_modification_square
    π hπ g ρ q hsquare η β hβ W hηW hnormY hnormB c f d hd D hklt cT
  have hcompat := subKltBasePrimeDiscriminantCoefficients_eq_effective g hnormY c f d hd D hklt
    hnormX hcov heff
  change subKltBasePrimeDiscriminantCoefficients q hnormB cT
    (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) _ β = _
  rw [← heq, hcompat]
  rfl

/-- The constructed rational Weil divisor is the unique one with these canonical coefficients. -/
theorem existsUnique_modified_base_canonical_discriminant :
    let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
    ∃! Δ : CodimensionOnePoint B →₀ ℚ, ∀ β,
      Δ β = subKltBasePrimeDiscriminantCoefficients q hnormB cT
        (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT β := by
  dsimp only
  refine ⟨modifiedBaseCanonicalSubKltDiscriminantWeilDivisor π hπ g ρ q hsquare W hW hnormY hnormX hnormB c f d hd D heff hklt cT, fun β => rfl, ?_⟩
  intro Δ hΔ
  ext β
  exact hΔ β

end MixedFujita
