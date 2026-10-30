/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalSubKltGlobalBaseTests
public import MixedFujita.BaseModificationThresholdComparison
public import MixedFujita.SubKltDiscriminantCoefficients

/-!
Canonical local thresholds and discriminant coefficients agree across compatible proper
crepant source/base modifications at corresponding normal base primes where the base
modification is locally an isomorphism. A global coefficient-one Cartier equation and its
actual effective neighbourhood connect both independently normalized local constructions
to the same rational tests. Negative crepant boundary coefficients are allowed.
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
  [IsNoetherian X] [IsNoetherian T] [IsLocallyNoetherian Y] [IsLocallyNoetherian B]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of K))]
  [IsSeparated (T ↘ Spec (CommRingCat.of K))]
  (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (g : X ⟶ Y) [IsDominant g] [IsProper g] (ρ : B ⟶ Y) [IsDominant ρ]
  (q : T ⟶ B) [IsDominant q] [IsProper q] (hsquare : q ≫ ρ = π ≫ g)
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
  (β : CodimensionOnePoint B) [IsIntegrallyClosed (B.presheaf.stalk (β : B))]
  (hβ : ρ (β : B) = (η : Y)) (W : Y.Opens) [IsIso (ρ ∣_ W)] (hηW : (η : Y) ∈ W)

include hsquare hβ hηW

/-- The independently normalized canonical local thresholds agree across the actual
compatible modification square at corresponding normal base primes. -/
theorem canonicalSubKltBasePrimeThreshold_eq_of_compatible_modification_square
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n) :
    let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
    canonicalSubKltBasePrimeThreshold g η c f d hd D hklt =
      canonicalSubKltBasePrimeThreshold q β cT (crepantPullbackFormUnit π hπ c f cT)
        d hd (cartierPullback π D) hkltT := by
  dsimp only
  let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
  obtain ⟨U, hUW, hηU, H, hHη, heff⟩ :=
    normal_base_prime_global_cartier_with_effective_neighborhood η W hηW
  letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
  letI : IsDominant U.1.ι :=
    ⟨U.1.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let V : B.Opens := ρ ⁻¹ᵁ U.1
  have hβV : (β : B) ∈ V := by change ρ (β : B) ∈ U.1; rw [hβ]; exact hηU
  letI : Nonempty V := ⟨⟨(β : B), hβV⟩⟩
  letI : IsDominant V.ι :=
    ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have hβW : ρ (β : B) ∈ W := by rw [hβ]; exact hηW
  haveI : IsIntegrallyClosed (Y.presheaf.stalk (ρ (β : B))) := by rw [hβ]; infer_instance
  have hHβ : cartierCoefficient (cartierPullback ρ H) (β : B) = 1 := by
    rw [cartierPullback_coefficient_eq_of_isIso_base_restrict ρ W β hβW H, hβ, hHη]
  have heffV : (cartierPullback V.ι (cartierPullback ρ H)).IsEffective :=
    cartierPullback_effective_on_preimage_open ρ U.1 H heff
  have htestY := canonicalSubKltBasePrimeThreshold_global_klt_tests g η c f d hd D hklt
    U.1 hηU H hHη heff
  have htestB := canonicalSubKltBasePrimeThreshold_global_klt_tests q β cT
    (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT
    V hβV (cartierPullback ρ H) hHβ heffV
  obtain ⟨a, q₀, ha, hq₀, heqY, -⟩ :=
    canonicalSubKltBasePrimeThreshold_realizes g η c f d hd D hklt
  obtain ⟨b, s₀, hb, hs₀, heqB, -⟩ :=
    canonicalSubKltBasePrimeThreshold_realizes q β cT
      (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT
  rw [heqY, heqB]
  apply rational_klt_threshold_eq_of_compatible_modification_square π hπ g ρ q hsquare
    W (β : B) hβW c f d hd D H cT a b q₀ s₀ hq₀ hs₀
  · intro p r hr
    simpa only [hβ, heqY] using htestY p r hr
  · intro p r hr
    simpa only [heqB] using htestB p r hr

/-- The actual canonical discriminant coefficient families agree at corresponding primes
of the same compatible source/base modification square. -/
theorem subKltBasePrimeDiscriminantCoefficients_eq_of_compatible_modification_square
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D) (cT : EtaleChart K T n) :
    let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
    subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η =
      subKltBasePrimeDiscriminantCoefficients q hnormB cT (crepantPullbackFormUnit π hπ c f cT)
        d hd (cartierPullback π D) hkltT β := by
  dsimp only
  change 1 - canonicalSubKltBasePrimeThreshold g η c f d hd D hklt = _
  rw [canonicalSubKltBasePrimeThreshold_eq_of_compatible_modification_square π hπ g ρ q hsquare
    η β hβ W hηW c f d hd D hklt cT]
  rfl

end MixedFujita
