/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalBasePrimeThresholdOneOpen

/-!
The now-constructed threshold-one open proves finite support of the actual
canonical discriminant coefficients. Construct their actual rational Weil
divisor as a finitely supported function, with its prescribed coefficients,
coefficient bounds and uniqueness. No finite-support or open certificate
is an input. Cartierness and the moduli part are separate obligations.
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
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D)

/-- The actual canonical discriminant coefficients have finite support, with no support certificate supplied. -/
theorem basePrimeDiscriminantCoefficients_finite_support :
    (Function.support
      (basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt)).Finite := by
  obtain ⟨V, hV, ht⟩ := exists_nonempty_open_canonicalBasePrimeKltThreshold_eq_one
    g hnormY hnorm hcov c f d hd D heff hklt
  exact (basePrimeDiscriminantCoefficients_finite_support_iff_threshold_one_open
    g hnormY hnorm hcov c f d hd D heff hklt).mpr ⟨V, hV, ht⟩

/-- The actual canonical rational discriminant Weil divisor, constructed from the original pair. -/
noncomputable def canonicalBasePrimeDiscriminantWeilDivisor : CodimensionOnePoint Y →₀ ℚ :=
  Finsupp.ofSupportFinite
    (basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt)
    (basePrimeDiscriminantCoefficients_finite_support g hnormY hnorm hcov c f d hd D heff hklt)

/-- Every coefficient is exactly one minus the actual canonical local klt threshold. -/
theorem canonicalBasePrimeDiscriminantWeilDivisor_apply (η : CodimensionOnePoint Y) :
    canonicalBasePrimeDiscriminantWeilDivisor g hnormY hnorm hcov c f d hd D heff hklt η =
      basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η := rfl

/-- All coefficients of the constructed rational Weil divisor lie in the half-open klt interval. -/
theorem canonicalBasePrimeDiscriminantWeilDivisor_coefficients_mem_Ico (η : CodimensionOnePoint Y) :
    canonicalBasePrimeDiscriminantWeilDivisor g hnormY hnorm hcov c f d hd D heff hklt η ∈
      Set.Ico (0 : ℚ) 1 :=
  basePrimeDiscriminantCoefficients_mem_Ico g hnorm hcov c f d hd D heff hklt hnormY η

/-- The original pair determines one unique rational Weil divisor with these canonical coefficients. -/
theorem existsUnique_canonical_base_prime_discriminant :
    ∃! B : CodimensionOnePoint Y →₀ ℚ,
      (∀ η, B η = basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η) ∧
      ∀ η, B η ∈ Set.Ico (0 : ℚ) 1 := by
  refine ⟨canonicalBasePrimeDiscriminantWeilDivisor g hnormY hnorm hcov c f d hd D heff hklt,
    ⟨fun η => rfl, canonicalBasePrimeDiscriminantWeilDivisor_coefficients_mem_Ico
      g hnormY hnorm hcov c f d hd D heff hklt⟩, ?_⟩
  intro B hB
  ext η
  exact hB.1 η

end MixedFujita
