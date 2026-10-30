/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DominantCartierGlobalGenerationPullback
public import MixedFujita.SNCModelFreeKltPerturbations

/-!
An ample class on another variety supplies a rational klt perturbation on the
source via a dominant pullback. Only global generation of a suitable pulled
multiple is used. In particular, the pulled divisor need not be ample or big,
and the source boundary may have negative coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Z : Scheme.{u}}
  [IsIntegral X] [IsIntegral Z]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A rational ample pullback has an actual klt cut in the exact pulled class,
with arbitrarily large common denominator and finite point avoidance. -/
theorem logPairIsKlt_exists_rational_pullback_ample_perturbation
    (h : X ⟶ Z) [IsDominant h]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (A : CartierDivisor Z) (hA : CartierIsAmpleProj K A)
    (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (ε : ℚ) (hε : 0 < ε)
    (P : Set X) (hP : P.Finite) :
    ∃ (m r : ℕ) (s : Γ((r • cartierPullback h A).sheaf, ⊤)) (hs : s ≠ 0),
      2 ≤ m ∧ 1 ≤ r ∧ m * d = r * q ∧ N ≤ m * d ∧ 1 < m * d ∧
      0 < 1 / ((m * d : ℕ) : ℚ) ∧ 1 / ((m * d : ℕ) : ℚ) < ε ∧
      LogPairIsKlt c f (m * d)
        (m • D + cartierSectionZeroDivisor (r • cartierPullback h A) s hs) ∧
      q • (m • D + cartierSectionZeroDivisor (r • cartierPullback h A) s hs) =
        m • (q • D + d • cartierPullback h A) +
          principalCartierDivisor X (cartierSectionUnit (r • cartierPullback h A) s hs ^ q) ∧
      (∀ x ∈ P, x ∉ cartierSectionZeroLocus (r • cartierPullback h A) s) := by
  obtain ⟨m, r, hm, hr, heq, hN, hmd, hpos, hsmall, hgen⟩ :=
    cartierIsAmpleProj_exists_common_denominator_global_generation A hA d q N hd hq ε hε
  have hgen' : CartierIsGloballyGenerated (r • cartierPullback h A) := by
    simpa only [cartierPullback_nsmul] using
      cartierIsGloballyGenerated_dominant_pullback h (r • A) hgen
  have hscaled := (logPairIsKlt_scale_denominator_iff c f d m (by omega) D).mpr hklt
  obtain ⟨s, hs, hklt', havoid⟩ := logPairIsKlt_exists_source_perturbation_avoiding
    hnorm c f (m * d) (m • D) hscaled (r • cartierPullback h A) hgen' 1 hmd P hP
  refine ⟨m, r, s, hs, hm, hr, heq, hN, hmd, hpos, hsmall, ?_, ?_, havoid⟩
  · simpa only [one_nsmul] using hklt'
  · exact cartierSection_common_denominator_perturbation_identity D (cartierPullback h A)
      d q m r heq s hs

end MixedFujita
