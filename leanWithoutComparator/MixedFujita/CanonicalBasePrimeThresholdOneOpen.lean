/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineBasePrimeGlobalUniformizer
public import MixedFujita.CanonicalBasePrimeThresholdOneCriterion
public import MixedFujita.OriginalKltBasePrimeLogCanonicalOpen
public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.DiscriminantFiniteSupportReduction

/-!
Construct a nonempty open of the original base on which every canonical
base-prime threshold is one. Choose one affine base neighbourhood first,
apply the original-pair coefficient-one lc theorem there, and use global
regular numerators of uniformizers. The original canonical local tests
compare this fixed actual restriction directly; no threshold-invariance
certificate or threshold-one open is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The original effective klt pair has canonical base-prime threshold one on a nonempty actual base open. -/
theorem exists_nonempty_open_canonicalBasePrimeKltThreshold_eq_one
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : X ⟶ Y) [IsProper g] [IsDominant g]
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ η : CodimensionOnePoint Y, (η : Y) ∈ V →
      letI := hnormY (η : Y)
      canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = 1 := by
  classical
  obtain ⟨_, ⟨U₀, hU, rfl⟩, hgenU, _⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial) (⊤ : Y.Opens).isOpen
  let U : Y.Opens := U₀
  letI : Nonempty U := ⟨⟨genericPoint Y, hgenU⟩⟩
  letI : IsAffine U.toScheme := hU
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U).ι :=
    ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
  letI : U.toScheme.Over (Spec (CommRingCat.of K)) := ⟨U.ι ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType (U.ι ≫ (Y ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ U).toScheme :=
    (g ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
  have hnormU : ∀ y : U.toScheme, IsIntegrallyClosed (U.toScheme.presheaf.stalk y) :=
    integrallyClosed_stalk_of_openImmersion U.ι hnormY
  obtain ⟨cU⟩ := exists_etaleChart_on_integral_open_immersion (g ⁻¹ᵁ U).ι c
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (g ⁻¹ᵁ U).ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι
  let fU := crepantPullbackFormUnit (g ⁻¹ᵁ U).ι hj c f cU
  let DU := cartierPullback (g ⁻¹ᵁ U).ι D
  have hkltU := logPairIsKlt_crepant_pullback_without_properness (g ⁻¹ᵁ U).ι hj
    c f d hd D hklt cU
  obtain ⟨W, hgenW, hW⟩ := exists_original_klt_base_prime_coefficient_one_logCanonical_open
    (g ∣_ U) hnormU cU fU d hd DU hkltU
  let V : Y.Opens := U.ι ''ᵁ W
  refine ⟨V, ⟨U.ι (genericPoint U.toScheme), genericPoint U.toScheme, hgenW, rfl⟩, ?_⟩
  intro η hηV
  letI := hnormY (η : Y)
  obtain ⟨θ, hθW, hθη⟩ := hηV
  have hηU : (η : Y) ∈ U := by
    rw [← hθη]
    exact θ.property
  let θ' : U.toScheme := ⟨(η : Y), hηU⟩
  have hθ'eq : θ' = θ := Subtype.ext hθη.symm
  have hθ'W : θ' ∈ W := hθ'eq.symm ▸ hθW
  have hθ' : Order.coheight θ' = 1 :=
    (coheight_eq_of_stalkMap_bijective U.ι θ'
      (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap θ'))).trans η.property
  letI := hnormU θ'
  obtain ⟨H, hH, fH, hfH, a, ha, hairred, hHθ⟩ :=
    affine_base_prime_exists_effective_cartier_uniformizer (⟨θ', hθ'⟩ : CodimensionOnePoint U.toScheme)
  have hlc := hW ⟨θ', hθ'⟩ hθ'W H hH fH hfH a ha hairred
  exact canonicalBasePrimeKltThreshold_eq_one_of_local_logCanonical
    g η hnorm hcov c f d hd D heff hklt U hηU H hH hHθ cU hlc

end MixedFujita
