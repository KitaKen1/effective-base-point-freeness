/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalSubKltBaseModificationComparison
public import MixedFujita.CanonicalBasePrimeThresholdOneOpen
public import MixedFujita.DiscriminantFiniteSupportReduction
public import MixedFujita.NormalCodimensionOneCharts

/-!
The canonical threshold-one open transfers from an original effective klt pair to a
compatible proper crepant source/base modification. Intersect the original open with
the base isomorphism neighbourhood and take its actual inverse image. Every base prime
there has an isomorphic normal codimension-one image and the same canonical threshold.
This proves finite support on the modified base even though its source boundary may
have negative coefficients. No general negative-boundary finite-support theorem is used.
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

/-- Transfer the actual original threshold-one open to the compatible modified base.
The source crepant boundary is allowed to have negative coefficients. -/
theorem exists_modified_base_open_canonicalSubKltBasePrimeThreshold_eq_one :
    let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
    ∃ V : B.Opens, genericPoint B ∈ V ∧ ∀ β : CodimensionOnePoint B, (β : B) ∈ V →
      letI := hnormB (β : B)
      canonicalSubKltBasePrimeThreshold q β cT (crepantPullbackFormUnit π hπ c f cT)
        d hd (cartierPullback π D) hkltT = 1 := by
  dsimp only
  let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
  have hcov : CodimOneChartCovered n K X :=
    normal_codimOneChartCovered (K := K) (etaleChart_topologicalKrullDim c) hnormX
  obtain ⟨V₀, hV₀, ht⟩ := exists_nonempty_open_canonicalBasePrimeKltThreshold_eq_one
    g hnormY hnormX hcov c f d hd D heff hklt
  have hgenV₀ : genericPoint Y ∈ V₀ := by
    apply ((genericPoint_spec Y).mem_open_set_iff V₀.isOpen).mpr
    obtain ⟨y, hy⟩ := hV₀
    exact ⟨y, Set.mem_univ y, hy⟩
  let V : B.Opens := ρ ⁻¹ᵁ (V₀ ⊓ W)
  have hgenV : genericPoint B ∈ V := by
    change ρ (genericPoint B) ∈ V₀ ⊓ W
    rw [dominant_map_genericPoint]
    exact ⟨hgenV₀, hW⟩
  refine ⟨V, hgenV, ?_⟩
  intro β hβV
  letI := hnormB (β : B)
  have hβV₀ : ρ (β : B) ∈ V₀ := hβV.1
  have hβW : ρ (β : B) ∈ W := hβV.2
  have hiso : IsIso (ρ.stalkMap (β : B)) := isIso_stalkMap_of_isIso_base_restrict ρ W β hβW
  have hη : Order.coheight (ρ (β : B)) = 1 :=
    (coheight_eq_of_stalkMap_bijective ρ β
      (ConcreteCategory.bijective_of_isIso (ρ.stalkMap (β : B)))).symm.trans β.property
  let η : CodimensionOnePoint Y := ⟨ρ (β : B), hη⟩
  letI := hnormY (η : Y)
  have heq := canonicalSubKltBasePrimeThreshold_eq_of_compatible_modification_square
    π hπ g ρ q hsquare η β rfl W hβW c f d hd D hklt cT
  calc
    canonicalSubKltBasePrimeThreshold q β cT (crepantPullbackFormUnit π hπ c f cT)
        d hd (cartierPullback π D) hkltT = canonicalSubKltBasePrimeThreshold g η c f d hd D hklt := heq.symm
    _ = canonicalBasePrimeKltThreshold g η hnormX hcov c f d hd D heff hklt :=
      canonicalSubKltBasePrimeThreshold_eq_effective_canonical g η c f d hd D hklt hnormX hcov heff
    _ = 1 := ht η hβV₀

/-- The actual canonical sub-klt discriminant coefficients have finite support on the
modified base, derived from the original effective pair and the compatible square. -/
theorem modified_base_subKlt_discriminant_coefficients_finite_support :
    let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
    (Function.support (subKltBasePrimeDiscriminantCoefficients q hnormB cT
      (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT)).Finite := by
  dsimp only
  let hkltT := logPairIsKlt_crepant_pullback_without_properness π hπ c f d hd D hklt cT
  obtain ⟨V, hgenV, ht⟩ := exists_modified_base_open_canonicalSubKltBasePrimeThreshold_eq_one
    π hπ g ρ q hsquare W hW hnormY hnormX hnormB c f d hd D heff hklt cT
  apply (codimensionOneCoefficients_finite_support_iff_nonempty_zero_open _).mpr
  refine ⟨V, ⟨genericPoint B, hgenV⟩, ?_⟩
  intro β hβ
  letI := hnormB (β : B)
  exact (subKltBasePrimeDiscriminantCoefficients_eq_zero_iff q hnormB cT
    (crepantPullbackFormUnit π hπ c f cT) d hd (cartierPullback π D) hkltT β).mpr (ht β hβ)

end MixedFujita
