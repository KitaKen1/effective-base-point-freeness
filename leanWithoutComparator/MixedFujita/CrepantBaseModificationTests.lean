/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BaseModificationSpecialization
public import MixedFujita.CrepantRationalThresholdComparison

/-!
The actual rational klt and lc tests agree across a compatible source/base modification
square at every point where the base modification is locally an isomorphism. The source
modification is proper crepant, and no boundary-effectivity hypothesis is used.
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
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of K))]
  [IsSeparated (T ↘ Spec (CommRingCat.of K))]
  (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (g : X ⟶ Y) [IsDominant g] (ρ : B ⟶ Y) [IsDominant ρ]
  (q : T ⟶ B) [IsDominant q] (hsquare : q ≫ ρ = π ≫ g)
  (U : Y.Opens) [IsIso (ρ ∣_ U)] (β : B) (hβ : ρ β ∈ U)

include hsquare hβ

/-- All rational klt tests agree across the actual compatible square, with the base
Cartier divisor pulled back along the base modification. -/
theorem rational_klt_overBasePoint_iff_compatible_modification_square
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (cT : EtaleChart K T n)
    (a b : ℕ) (hb : 1 ≤ b) :
    LogPairIsKltOverBasePoint g (ρ β) c f (b * d)
      (b • D + (d * a) • cartierPullback g H) ↔
      LogPairIsKltOverBasePoint q β cT (crepantPullbackFormUnit π hπ c f cT) (b * d)
        (b • cartierPullback π D + (d * a) • cartierPullback q (cartierPullback ρ H)) := by
  have hdiv : cartierPullback (π ≫ g) H = cartierPullback q (cartierPullback ρ H) := by
    simpa only [hsquare] using cartierPullback_comp ρ q H
  have h := rational_klt_overBasePoint_iff_proper_crepant_pullback π hπ g (ρ β)
    c f d hd D H cT a b hb
  rw [hdiv] at h
  have h' : LogPairIsKltOverBasePoint g (ρ β) c f (b * d)
      (b • D + (d * a) • cartierPullback g H) ↔
      LogPairIsKltOverBasePoint (q ≫ ρ) (ρ β) cT (crepantPullbackFormUnit π hπ c f cT) (b * d)
        (b • cartierPullback π D + (d * a) • cartierPullback q (cartierPullback ρ H)) := by
    simpa only [hsquare] using h
  exact h'.trans (logPairIsKltOverBasePoint_comp_isIso_base_restrict_iff q ρ U β hβ
    cT (crepantPullbackFormUnit π hπ c f cT) (b * d)
      (b • cartierPullback π D + (d * a) • cartierPullback q (cartierPullback ρ H)))

/-- The non-strict lc tests agree across the same actual modification square. -/
theorem rational_logCanonical_overBasePoint_iff_compatible_modification_square
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (cT : EtaleChart K T n)
    (a b : ℕ) (hb : 1 ≤ b) :
    LogPairIsLogCanonicalOverBasePoint g (ρ β) c f (b * d)
      (b • D + (d * a) • cartierPullback g H) ↔
      LogPairIsLogCanonicalOverBasePoint q β cT (crepantPullbackFormUnit π hπ c f cT) (b * d)
        (b • cartierPullback π D + (d * a) • cartierPullback q (cartierPullback ρ H)) := by
  have hdiv : cartierPullback (π ≫ g) H = cartierPullback q (cartierPullback ρ H) := by
    simpa only [hsquare] using cartierPullback_comp ρ q H
  have h := rational_logCanonical_overBasePoint_iff_proper_crepant_pullback π hπ g (ρ β)
    c f d hd D H cT a b hb
  rw [hdiv] at h
  have h' : LogPairIsLogCanonicalOverBasePoint g (ρ β) c f (b * d)
      (b • D + (d * a) • cartierPullback g H) ↔
      LogPairIsLogCanonicalOverBasePoint (q ≫ ρ) (ρ β) cT (crepantPullbackFormUnit π hπ c f cT) (b * d)
        (b • cartierPullback π D + (d * a) • cartierPullback q (cartierPullback ρ H)) := by
    simpa only [hsquare] using h
  exact h'.trans (logPairIsLogCanonicalOverBasePoint_comp_isIso_base_restrict_iff q ρ U β hβ
    cT (crepantPullbackFormUnit π hπ c f cT) (b * d)
      (b • cartierPullback π D + (d * a) • cartierPullback q (cartierPullback ρ H)))

end MixedFujita
