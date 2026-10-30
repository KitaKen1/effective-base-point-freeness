/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaPrincipalizingRound

/-!
A modification which is an isomorphism over a target neighbourhood reflects the
specialization guard at a point over that neighbourhood. The other point need not be
assumed to lie in the neighbourhood: specialization forces this. Hence the actual
base-point-filtered klt and lc predicates are unchanged by this base modification.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A target-neighbourhood isomorphism reflects specialization to a point above it. -/
theorem mem_closure_singleton_iff_of_isIso_base_restrict {B Y : Scheme.{u}}
    (ρ : B ⟶ Y) (U : Y.Opens) [IsIso (ρ ∣_ U)] (b β : B) (hβ : ρ β ∈ U) :
    ρ β ∈ closure ({ρ b} : Set Y) ↔ β ∈ closure ({b} : Set B) := by
  rw [← specializes_iff_mem_closure, ← specializes_iff_mem_closure]
  constructor
  · intro h
    have hb : ρ b ∈ U := h.mem_open U.isOpen hβ
    let b' : (ρ ⁻¹ᵁ U).toScheme := ⟨b, hb⟩
    let β' : (ρ ⁻¹ᵁ U).toScheme := ⟨β, hβ⟩
    have hrest : (ρ ∣_ U) b' ⤳ (ρ ∣_ U) β' := by
      apply U.ι.isOpenEmbedding.isInducing.specializes_iff.mp
      change ((ρ ∣_ U) b').1 ⤳ ((ρ ∣_ U) β').1
      simpa only [morphismRestrict_base_coe] using h
    have hsrc : b' ⤳ β' := (ρ ∣_ U).homeomorph.isInducing.specializes_iff.mp hrest
    exact hsrc.map (ρ ⁻¹ᵁ U).ι.continuous
  · intro h
    exact h.map ρ.continuous

/-- The actual stalk map is an isomorphism at every point over the isomorphism neighbourhood. -/
theorem isIso_stalkMap_of_isIso_base_restrict {B Y : Scheme.{u}}
    (ρ : B ⟶ Y) (U : Y.Opens) [IsIso (ρ ∣_ U)] (β : B) (hβ : ρ β ∈ U) :
    IsIso (ρ.stalkMap β) := by
  have h : IsIso ((ρ ∣_ U).stalkMap ⟨β, hβ⟩) := inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (morphismRestrictStalkMap ρ U ⟨β, hβ⟩)).mp h

variable {K : Type u} [Field K] {n : ℕ} {X B Y : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  (g : X ⟶ B) (ρ : B ⟶ Y) (U : Y.Opens) [IsIso (ρ ∣_ U)]
  (β : B) (hβ : ρ β ∈ U)

include hβ

/-- Base-point klt is unchanged by composing with a modification which is locally an
isomorphism above the chosen point. -/
theorem logPairIsKltOverBasePoint_comp_isIso_base_restrict_iff
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    LogPairIsKltOverBasePoint (g ≫ ρ) (ρ β) c f d D ↔
      LogPairIsKltOverBasePoint g β c f d D := by
  constructor
  · intro h T _ _ _ _ σ _ _ _ hσ cT t ht hguard
    apply h T σ hσ cT t ht
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using
      (mem_closure_singleton_iff_of_isIso_base_restrict ρ U ((σ ≫ g) t) β hβ).mpr hguard
  · intro h T _ _ _ _ σ _ _ _ hσ cT t ht hguard
    apply h T σ hσ cT t ht
    apply (mem_closure_singleton_iff_of_isIso_base_restrict ρ U ((σ ≫ g) t) β hβ).mp
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using hguard

/-- The same local base modification preserves the non-strict lc predicate. -/
theorem logPairIsLogCanonicalOverBasePoint_comp_isIso_base_restrict_iff
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) :
    LogPairIsLogCanonicalOverBasePoint (g ≫ ρ) (ρ β) c f d D ↔
      LogPairIsLogCanonicalOverBasePoint g β c f d D := by
  constructor
  · intro h T _ _ _ _ σ _ _ _ hσ cT t ht hguard
    apply h T σ hσ cT t ht
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using
      (mem_closure_singleton_iff_of_isIso_base_restrict ρ U ((σ ≫ g) t) β hβ).mpr hguard
  · intro h T _ _ _ _ σ _ _ _ hσ cT t ht hguard
    apply h T σ hσ cT t ht
    apply (mem_closure_singleton_iff_of_isIso_base_restrict ρ U ((σ ≫ g) t) β hβ).mp
    simpa only [Category.assoc, Scheme.Hom.comp_apply] using hguard

end MixedFujita
