/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantBaseModificationTests
public import MixedFujita.NormalBirationalPrimeLifts

/-!
Coefficient normalization and exact finite endpoint values are preserved across compatible
modification squares at points where the base modification is locally an isomorphism.
The coefficient comparison uses the actual stalk map; endpoint equality compares all
actual rational klt tests and evaluates the two endpoint ratios.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The base modification preserves actual Cartier coefficients at a prime above its
isomorphism neighbourhood. In particular coefficient-one equations stay normalized. -/
theorem cartierPullback_coefficient_eq_of_isIso_base_restrict
    {B Y : Scheme.{u}} [IsIntegral B] [IsIntegral Y]
    [IsLocallyNoetherian B] [IsLocallyNoetherian Y]
    (ρ : B ⟶ Y) [IsDominant ρ] (U : Y.Opens) [IsIso (ρ ∣_ U)]
    (β : CodimensionOnePoint B) [IsIntegrallyClosed (Y.presheaf.stalk (ρ (β : B)))]
    (hβ : ρ (β : B) ∈ U) (H : CartierDivisor Y) :
    cartierCoefficient (cartierPullback ρ H) (β : B) = cartierCoefficient H (ρ (β : B)) := by
  have hiso : IsIso (ρ.stalkMap (β : B)) := isIso_stalkMap_of_isIso_base_restrict ρ U β hβ
  have hcod : Order.coheight (ρ (β : B)) = 1 :=
    (coheight_eq_of_stalkMap_bijective ρ β
      (ConcreteCategory.bijective_of_isIso (ρ.stalkMap (β : B)))).symm.trans β.property
  haveI := normal_codimensionOne_stalk_DVR (⟨ρ (β : B), hcod⟩ : CodimensionOnePoint Y)
  haveI : IsDiscreteValuationRing (B.presheaf.stalk (β : B)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective (ρ.stalkMap (β : B)).hom
        (ConcreteCategory.bijective_of_isIso (ρ.stalkMap (β : B))))
  exact cartierCoefficient_pullback_of_stalkMap_bijective ρ β hcod
    (ConcreteCategory.bijective_of_isIso (ρ.stalkMap (β : B))) H

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

/-- Finite endpoints from the two actual rational klt intervals agree across a
compatible source/base modification square. -/
theorem rational_klt_threshold_eq_of_compatible_modification_square
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (cT : EtaleChart K T n)
    (a b q₀ s₀ : ℕ) (hq₀ : 1 ≤ q₀) (hs₀ : 1 ≤ s₀)
    (ha : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g (ρ β) c f (r * d)
        (r • D + (d * p) • cartierPullback g H) ↔ (p : ℚ) / r < (a : ℚ) / q₀))
    (hb : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint q β cT (crepantPullbackFormUnit π hπ c f cT) (r * d)
        (r • cartierPullback π D + (d * p) • cartierPullback q (cartierPullback ρ H)) ↔
          (p : ℚ) / r < (b : ℚ) / s₀)) :
    (a : ℚ) / q₀ = (b : ℚ) / s₀ := by
  have htest (p r : ℕ) (hr : 1 ≤ r) :
      (p : ℚ) / r < (a : ℚ) / q₀ ↔ (p : ℚ) / r < (b : ℚ) / s₀ :=
    (ha p r hr).symm.trans
      ((rational_klt_overBasePoint_iff_compatible_modification_square π hπ g ρ q hsquare
        U β hβ c f d hd D H cT p r hr).trans (hb p r hr))
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact (lt_irrefl _) ((htest a q₀ hq₀).mpr hab)
  · exact (lt_irrefl _) ((htest b s₀ hs₀).mp hba)

end MixedFujita
