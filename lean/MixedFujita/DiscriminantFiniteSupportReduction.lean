/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalBasePrimeThresholdUpperBound
public import MixedFujita.IntegralCurveFiniteComplement

/-!
The finite-support obligation for the actual canonical discriminant family is
exactly the existence of a nonempty base open on whose primes the threshold is
one. Proper dominance supplies Noetherianity of the actual target. Given such
an open, construct the unique rational Weil divisor with the prescribed
coefficients. Existence of that open is not assumed to have been proved.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A proper dominant image of a Noetherian integral scheme is Noetherian. -/
theorem proper_dominant_noetherian_target {X Y : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsProper g] [IsDominant g] : IsNoetherian Y := by
  letI : NoetherianSpace Y := noetherianSpace_of_surjective g g.continuous
    (surjective_of_isProper_of_isDominant g)
  constructor <;> infer_instance

/-- Any nonempty open of an integral Noetherian scheme misses only finitely many primes. -/
theorem codimensionOnePoints_outside_nonempty_open_finite
    {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) :
    {η : CodimensionOnePoint Y | (η : Y) ∉ U}.Finite := by
  let Z : Set Y := (U : Set Y)ᶜ
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  letI : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hproper : closure Z ≠ Set.univ := by
    rw [hZ.closure_eq]
    obtain ⟨y, hy⟩ := hU
    intro h
    have : y ∈ Z := h.symm ▸ Set.mem_univ y
    exact this hy
  have hfin := NoetherianSpace.finite_coheight_one_of_closure_ne_univ hproper
  convert Set.Finite.preimage_embedding
    (Function.Embedding.subtype fun y : Y => Order.coheight y = 1) hfin using 1
  ext η
  change ((η : Y) ∉ U) ↔ ((η : Y) ∈ Z ∧ Order.coheight (η : Y) = 1)
  simp only [η.property, and_true]
  rfl

/-- Finite primewise coefficients are equivalent to vanishing on a nonempty actual open. -/
theorem codimensionOneCoefficients_finite_support_iff_nonempty_zero_open
    {Y : Scheme.{u}} [IsIntegral Y] [IsNoetherian Y]
    (b : CodimensionOnePoint Y → ℚ) :
    (Function.support b).Finite ↔ ∃ U : Y.Opens, (U : Set Y).Nonempty ∧
      ∀ η : CodimensionOnePoint Y, (η : Y) ∈ U → b η = 0 := by
  classical
  constructor
  · intro hfin
    let Z : Set Y := ⋃ η ∈ Function.support b, closure ({(η : Y)} : Set Y)
    have hZ : IsClosed Z := hfin.isClosed_biUnion (fun _ _ => isClosed_closure)
    have hgen : genericPoint Y ∉ Z := by
      intro h
      obtain ⟨η, _, hη⟩ := Set.mem_iUnion₂.mp h
      exact genericPoint_notMem_closure_of_coheight_eq_one η.property hη
    refine ⟨⟨Zᶜ, hZ.isOpen_compl⟩, ⟨genericPoint Y, hgen⟩, ?_⟩
    intro η hη
    by_contra hne
    exact hη (Set.mem_iUnion₂.mpr ⟨η, hne, subset_closure rfl⟩)
  · rintro ⟨U, hU, hb⟩
    apply (codimensionOnePoints_outside_nonempty_open_finite U hU).subset
    intro η hη hηU
    exact hη (hb η hηU)

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D)

/-- The remaining geometric finite-support problem is exactly a threshold-one base open. -/
theorem basePrimeDiscriminantCoefficients_finite_support_iff_threshold_one_open :
    (Function.support
      (basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt)).Finite ↔
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ ∀ η : CodimensionOnePoint Y, (η : Y) ∈ U →
      letI := hnormY (η : Y)
      canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = 1 := by
  letI : IsNoetherian Y := proper_dominant_noetherian_target g
  rw [codimensionOneCoefficients_finite_support_iff_nonempty_zero_open]
  constructor
  · rintro ⟨U, hU, hb⟩
    refine ⟨U, hU, ?_⟩
    intro η hη
    letI := hnormY (η : Y)
    exact (basePrimeDiscriminantCoefficients_eq_zero_iff
      g hnormY hnorm hcov c f d hd D heff hklt η).mp (hb η hη)
  · rintro ⟨U, hU, ht⟩
    refine ⟨U, hU, ?_⟩
    intro η hη
    letI := hnormY (η : Y)
    exact (basePrimeDiscriminantCoefficients_eq_zero_iff
      g hnormY hnorm hcov c f d hd D heff hklt η).mpr (ht η hη)

/-- A threshold-one base open constructs the unique actual rational Weil divisor.
Existence of this open remains the unsolved geometric obligation. -/
theorem existsUnique_rational_discriminant_of_threshold_one_open
    (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    (ht : ∀ η : CodimensionOnePoint Y, (η : Y) ∈ U → letI := hnormY (η : Y)
      canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = 1) :
    ∃! B : CodimensionOnePoint Y →₀ ℚ,
      (∀ η, B η = basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η) ∧
      ∀ η, B η ∈ Set.Ico (0 : ℚ) 1 := by
  have hfin := (basePrimeDiscriminantCoefficients_finite_support_iff_threshold_one_open
    g hnormY hnorm hcov c f d hd D heff hklt).mpr ⟨U, hU, ht⟩
  refine ⟨Finsupp.ofSupportFinite _ hfin, ⟨fun η => rfl, ?_⟩, ?_⟩
  · intro η
    exact basePrimeDiscriminantCoefficients_mem_Ico g hnorm hcov c f d hd D heff hklt hnormY η
  · intro B hB
    ext η
    exact hB.1 η

end MixedFujita
