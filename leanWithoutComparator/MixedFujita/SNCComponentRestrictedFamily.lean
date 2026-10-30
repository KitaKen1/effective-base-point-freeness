/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCInducedSignedResidual
public import MixedFujita.HironakaSNCDictionary
public import MixedFujita.PointBlowupCentreCoefficient
public import MixedFujita.SNCPointDivisorFamily
public import MixedFujita.DVRVanishingOrder
public import Hironaka.Scheme.Snc.EraseFamily
public import Hironaka.Scheme.Snc.RestrictHypersurface
public import Hironaka.Scheme.BlowUpSequence.PullbackSnc
public import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Center
public import Hironaka.Scheme.BlowUp.Transform.StrictTransform
public import Hironaka.Scheme.BlowUp.Descent
public import Hironaka.Scheme.IdealSheaf.Order.Along
public import Hironaka.Scheme.Snc.DictionaryOrder

/-!
The other members of a simple normal crossing family restricted to one of its members
(step 16E).

Let ξ be an SNC family of prime divisors on a smooth scheme T and S the member ξ i₀. On an
integral open and closed piece U of the stratum of S, with j : U → T the closed immersion:

* the other members, pulled back to U, form a simple normal crossing family
  (Kollár's `E_S = (E − E^{i₀})|_S`, via the vendored resolution library);
* at a codimension-one point t of U at most one other member passes through j t, and the
  induced effective divisor of that member has coefficient one at t; the induced divisor of a
  member not passing through j t has coefficient zero;
* the codimension-one points of U lying over the other members are part of an SNC family on U
  in the sense of this project.

These are the coefficient and SNC inputs of Kawamata–Viehweg vanishing on the lc place S.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

attribute [local instance] Classical.propDecidable

/-- **Kollár's restricted family.** The other members of a simple normal crossing family,
pulled back to one member, form a simple normal crossing family on it. -/
theorem divisorFamily_erase_comap_component_isSnc {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f]
    (E : Scheme.DivisorFamily X) (hE : E.IsSnc) (j : E.ι) :
    ((E.erase j).comap (E.component j).subschemeι).IsSnc := by
  set ι := (E.component j).subschemeι with hιdef
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x =>
    isRegularLocalRing_stalk f x
  have hE' : ((E.erase j).append ι.ker).IsSnc := by
    rw [hιdef, Scheme.IdealSheafData.ker_subschemeι]
    exact Scheme.DivisorFamily.isSnc_erase_append E j hE
  have hZ : ((E.erase j).append ι.ker).HasSncWith ι.ker :=
    Scheme.DivisorFamily.hasSncWith_component _ hE'.2 (toLex (Sum.inr PUnit.unit))
  have h := hasSncWith_comap_of_isClosedImmersion ι hreg hZ le_rfl
  rw [hιdef, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.comap_subschemeι_eq_bot] at h
  have hat : ∀ y, ∃ (n : ℕ) (z : Fin n → _),
      ((E.erase j).comap (E.component j).subschemeι).IsSncAt y z := fun y => by
    obtain ⟨n, z, hz, -⟩ := h y (by rw [Scheme.IdealSheafData.support_bot]; trivial)
    exact ⟨n, z, hz⟩
  refine ⟨fun i => ?_, hat⟩
  have : Smooth ((E.component j).subschemeι ≫ f) :=
    Hironaka.Sequence.smooth_of_hasSncWith f
      (Scheme.DivisorFamily.hasSncWith_component E hE.2 j)
  exact Hironaka.Sequence.isRegular_subscheme_of_hasSncWith ((E.component j).subschemeι ≫ f)
    (Scheme.DivisorFamily.hasSncWith_component _ hat i)

/-- The stratum of one selected member is the vanishing ideal of that member. -/
theorem sncStratumIdeal_selected_singleton_eq {T : Scheme.{u}} {R : ℕ} (ξ : Fin R → T)
    (i₀ : Fin R) :
    sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ =
      (sncDivisorFamilyOfPoints ξ).component ⟨i₀⟩ := by
  have hsel : ∀ k, sncSelectedPoints ξ {i₀} k = ξ i₀ := by
    intro k
    simp only [sncSelectedPoints]
    rw [Finset.mem_singleton.mp ((Fintype.equivFin ({i₀} : Finset (Fin R))).symm k).prop]
  unfold sncStratumIdeal
  apply le_antisymm
  · refine iSup₂_le fun k _ => le_of_eq ?_
    change Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({sncSelectedPoints ξ {i₀} k.down} : Set T), isClosed_closure⟩ : Closeds T) =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i₀} : Set T), isClosed_closure⟩ : Closeds T)
    rw [hsel]
  · let k : ULift.{u} (Fin (Fintype.card ({i₀} : Finset (Fin R)))) :=
      ⟨Fintype.equivFin ({i₀} : Finset (Fin R)) ⟨i₀, Finset.mem_singleton_self i₀⟩⟩
    refine le_iSup₂_of_le (f := fun i (_ : i ∈ Finset.univ) =>
      (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})).component i) k (Finset.mem_univ k)
      (le_of_eq ?_)
    change Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i₀} : Set T), isClosed_closure⟩ : Closeds T) =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({sncSelectedPoints ξ {i₀} k.down} : Set T), isClosed_closure⟩ : Closeds T)
    rw [hsel]

variable {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]

/-- On an open piece of the stratum of one member, the other members pulled back form a simple
normal crossing family. -/
theorem snc_selected_singleton_open_restricted_isSnc [PerfectField K]
    [Smooth (T ↘ Spec (CommRingCat.of K))] {n R : ℕ} (ξ : Fin R → T)
    (hsnc : IsSNCFamily K n ξ) (i₀ : Fin R)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
      Finset.univ).subscheme.Opens) :
    ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap
      (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
        Finset.univ).subschemeι).comap U.ι).IsSnc := by
  have hE := sncDivisorFamilyOfPoints_isSnc (K := K) ξ hsnc
  have h0 := divisorFamily_erase_comap_component_isSnc (T ↘ Spec (CommRingCat.of K)) _ hE ⟨i₀⟩
  rw [← sncStratumIdeal_selected_singleton_eq ξ i₀] at h0
  have hζ := sncSelectedPoints_isSNCFamily ξ hsnc {i₀}
  have hsm : Smooth ((sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
      Finset.univ).subschemeι ≫ (T ↘ Spec (CommRingCat.of K))) :=
    Hironaka.Sequence.smooth_of_hasSncWith (T ↘ Spec (CommRingCat.of K))
      (sncStratumIdeal_hasSncWith _ (sncDivisorFamilyOfPoints_isSnc (K := K) _ hζ) Finset.univ)
  exact isSnc_comap_of_smooth ((sncStratumIdeal (sncDivisorFamilyOfPoints
    (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι ≫ (T ↘ Spec (CommRingCat.of K))) U.ι h0

/-- **Coefficients of the restricted members.** At a codimension-one point t of an integral
piece U of the stratum of ξ i₀, the induced divisor of another member has coefficient one when
the member passes through t and zero otherwise, and at most one other member passes through t. -/
theorem snc_selected_singleton_induced_coefficient [PerfectField K]
    [Smooth (T ↘ Spec (CommRingCat.of K))] {n R : ℕ} (ξ : Fin R → T)
    (hsnc : IsSNCFamily K n ξ) (i₀ : Fin R)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
      Finset.univ).subscheme.Opens)
    [IsIntegral U] [IsLocallyNoetherian U]
    (hreg : ∀ y : U.toScheme, IsRegularLocalRing (U.toScheme.presheaf.stalk y))
    (G : Fin R → CartierDivisor U) (hG : ∀ i, (G i).IsEffective)
    (hGI : ∀ i, i ≠ i₀ → effectiveCartierIdealSheaf (G i) (hG i) =
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T)).comap
        (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
          Finset.univ).subschemeι))
    (t : CodimensionOnePoint U) :
    (∀ i, i ≠ i₀ → cartierCoefficient (G i) t.1 =
        if (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
          Finset.univ).subschemeι) t.1 ∈ closure ({ξ i} : Set T) then 1 else 0) ∧
      ∀ i i', i ≠ i₀ → i' ≠ i₀ →
        (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
          Finset.univ).subschemeι) t.1 ∈ closure ({ξ i} : Set T) →
        (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀}))
          Finset.univ).subschemeι) t.1 ∈ closure ({ξ i'} : Set T) → i = i' := by
  have hFU := snc_selected_singleton_open_restricted_isSnc (K := K) ξ hsnc i₀ U
  have hcomp : ∀ i' : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι, ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i' = (Scheme.IdealSheafData.vanishingIdeal (⟨closure ({ξ i'.1.down} : Set T), isClosed_closure⟩ : Closeds T)).comap (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) := by
    intro i'
    rw [Scheme.IdealSheafData.comap_comp]
    rfl
  have hmem : ∀ i' : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι, t.1 ∈ (((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i').support ↔
      (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) t.1 ∈ closure ({ξ i'.1.down} : Set T) := by
    intro i'
    rw [hcomp i', Scheme.IdealSheafData.support_comap]
    change (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) t.1 ∈ ((Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i'.1.down} : Set T), isClosed_closure⟩ : Closeds T)).support : Set T) ↔ _
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨m, z, hz, c, hcinj, hc⟩ := hFU.2 t.1
  have hm : m = 1 := by
    have h := hz.2
    rw [ringKrullDim_stalk_eq_coheight, t.property] at h
    exact_mod_cast h
  subst hm
  let : IsRegularLocalRing (U.toScheme.presheaf.stalk t.1) := hreg t.1
  have hrange : Set.range z = {z 0} := by
    ext w
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, rfl⟩
      rw [Subsingleton.elim a 0]
    · rintro rfl
      exact ⟨0, rfl⟩
  have hmax : IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk t.1) = Ideal.span {z 0} := by
    rw [← hz.1, hrange]
  have hz0 : z 0 ≠ 0 := by
    intro h0
    have hbot : IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk t.1) = ⊥ := by
      rw [hmax, h0, Ideal.span_singleton_eq_bot.mpr rfl]
    have hdim := IsDiscreteValuationRing.not_a_field (U.toScheme.presheaf.stalk t.1)
    exact hdim hbot
  have hirr : Irreducible (z 0) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal (z 0) hz0 hmax
  have horder : localAdicOrder (U.toScheme.presheaf.stalk t.1) (z 0) = ((1 : ℕ) : ℕ∞) := by
    rw [dvr_localAdicOrder_eq_addVal, IsDiscreteValuationRing.addVal_uniformizer hirr]
    rfl
  refine ⟨fun i hi => ?_, fun i i' hi hi' hti hti' => ?_⟩
  · have hne : (⟨i⟩ : ULift.{u} (Fin R)) ≠ ⟨i₀⟩ := fun h => hi (congrArg ULift.down h)
    let i₁ : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι := ⟨⟨i⟩, hne⟩
    by_cases hti : (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) t.1 ∈ closure ({ξ i} : Set T)
    · rw [ite_eq_left hti]
      have htF : t.1 ∈ (((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i₁).support := (hmem i₁).mpr hti
      have hst : (effectiveCartierIdealSheaf (G i) (hG i)).stalkIdeal t.1 =
          Ideal.span {z 0} := by
        rw [hGI i hi, ← hcomp i₁, hc ⟨i₁, htF⟩, Subsingleton.elim (c ⟨i₁, htF⟩) 0]
      exact_mod_cast effectiveCartier_coefficient_of_stalkIdeal_span (G i) (hG i) t (z 0) hz0
        hst 1 horder
    · rw [ite_eq_right hti]
      apply cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf (G i) (hG i)
      rw [hGI i hi, ← hcomp i₁]
      exact fun h => hti ((hmem i₁).mp h)
  · have hne : (⟨i⟩ : ULift.{u} (Fin R)) ≠ ⟨i₀⟩ := fun h => hi (congrArg ULift.down h)
    have hne' : (⟨i'⟩ : ULift.{u} (Fin R)) ≠ ⟨i₀⟩ := fun h => hi' (congrArg ULift.down h)
    let i₁ : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι := ⟨⟨i⟩, hne⟩
    let i₂ : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι := ⟨⟨i'⟩, hne'⟩
    have h₁ : t.1 ∈ (((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i₁).support := (hmem i₁).mpr hti
    have h₂ : t.1 ∈ (((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i₂).support := (hmem i₂).mpr hti'
    have heq := hcinj (Subsingleton.elim (c ⟨i₁, h₁⟩) (c ⟨i₂, h₂⟩))
    have h12 : i₁ = i₂ := congrArg Subtype.val heq
    have := congrArg (fun a : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι => a.1.down) h12
    exact this

omit [IsIntegral T] [IsLocallyNoetherian T] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] in
/-- The support of a restricted member is the preimage of the member. -/
theorem snc_selected_singleton_restricted_member_support {R : ℕ} (ξ : Fin R → T) (i₀ : Fin R)
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subscheme.Opens) (i' : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι) (y : U.toScheme) :
    y ∈ (((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i').support ↔ (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) y ∈ closure ({ξ i'.1.down} : Set T) := by
  have hcomp : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i' = (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i'.1.down} : Set T), isClosed_closure⟩ : Closeds T)).comap (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) := by
    rw [Scheme.IdealSheafData.comap_comp]
    rfl
  rw [hcomp, Scheme.IdealSheafData.support_comap]
  change (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) y ∈ ((Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({ξ i'.1.down} : Set T), isClosed_closure⟩ : Closeds T)).support : Set T) ↔ _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **The restricted SNC family.** The codimension-one points of U lying over the other members
belong to an SNC family on U in the sense of this project. -/
theorem snc_selected_singleton_exists_restricted_snc_family [PerfectField K]
    [Smooth (T ↘ Spec (CommRingCat.of K))] {n R : ℕ} (ξ : Fin R → T)
    (hsnc : IsSNCFamily K n ξ) (i₀ : Fin R)
    [(sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subscheme.Over (Spec (CommRingCat.of K))]
    (U : (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subscheme.Opens) [IsIntegral U] {ℓ : ℕ}
    [SmoothOfRelativeDimension ℓ (U.toScheme ↘ Spec (CommRingCat.of K))]
    [NoetherianSpace U.toScheme]
    (havoid : ∀ i, i ≠ i₀ → (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) (genericPoint U) ∉ closure ({ξ i} : Set T)) :
    ∃ (r' : ℕ) (ζ : Fin r' → U.toScheme), Function.Injective ζ ∧
      (∀ k, Order.coheight (ζ k) = 1) ∧ IsSNCFamily K ℓ ζ ∧
      ∀ t : CodimensionOnePoint U, ∀ i, i ≠ i₀ →
        (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) t.1 ∈ closure ({ξ i} : Set T) → t.1 ∈ Set.range ζ := by
  have hFU := snc_selected_singleton_open_restricted_isSnc (K := K) ξ hsnc i₀ U
  have hsmU : Smooth (U.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth ℓ _
  have hB := Hironaka.Sequence.IsSnc.isSncBoundary_unionIdeal
    (U.toScheme ↘ Spec (CommRingCat.of K)) hFU
  -- a closed set containing all restricted members and avoiding the generic point
  let C : Closeds U.toScheme := ⟨⋃ i ∈ (Finset.univ.filter fun i : Fin R => i ≠ i₀),
      (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι) ⁻¹' closure ({ξ i} : Set T),
    isClosed_biUnion_finset fun i _ =>
      isClosed_closure.preimage (U.ι ≫ (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).continuous⟩
  have hFC : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).unionIdeal.support ≤ C := by
    rw [AlgebraicGeometry.support_unionIdeal]
    refine iSup_le fun i' => ?_
    intro y hy
    have h := (snc_selected_singleton_restricted_member_support ξ i₀ U i' y).mp hy
    have hne : i'.1.down ≠ i₀ := fun h' => i'.2 (ULift.ext h')
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩) h
  have hgenC : genericPoint U ∉ C := by
    intro h
    obtain ⟨i, hi, hJ⟩ := Set.mem_iUnion₂.mp h
    exact havoid i (Finset.mem_filter.mp hi).2 hJ
  let Γ : Set U.toScheme := {g | g ∈ ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).unionIdeal.support.genericPoints ∧ Order.coheight g = 1}
  have hΓ : Γ.Finite := (Closeds.genericPoints_finite ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).unionIdeal.support).subset fun g hg => hg.1
  let : Finite Γ := hΓ.to_subtype
  obtain ⟨r', ⟨e⟩⟩ := Finite.exists_equiv_fin Γ
  have hinj : Function.Injective (fun k => (e.symm k : U.toScheme)) := by
    intro k k' h
    exact e.symm.injective (Subtype.ext h)
  refine ⟨r', fun k => (e.symm k : U.toScheme), hinj, fun k => (e.symm k).2.2,
    isSNCFamily_of_isSncBoundary (K := K) (n := ℓ) _ hB _ hinj fun k => (e.symm k).2.1, ?_⟩
  intro t i hi hti
  have hne : (⟨i⟩ : ULift.{u} (Fin R)) ≠ ⟨i₀⟩ := fun h => hi (congrArg ULift.down h)
  let i₁ : ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).ι := ⟨⟨i⟩, hne⟩
  have htF : t.1 ∈ (((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i₁).support :=
    (snc_selected_singleton_restricted_member_support ξ i₀ U i₁ t.1).mpr hti
  have htZ : t.1 ∈ ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).unionIdeal.support := by
    rw [AlgebraicGeometry.support_unionIdeal]
    exact (le_iSup (fun i' => (((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).component i').support) i₁) htF
  have hgen : t.1 ∈ ((((sncDivisorFamilyOfPoints ξ).erase ⟨i₀⟩).comap (sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ).subschemeι).comap U.ι).unionIdeal.support.genericPoints := by
    refine ⟨htZ, fun η' hη' hsp => ?_⟩
    by_contra hne'
    have hle : t.1 ≤ η' := Scheme.le_iff_specializes.mpr hsp
    have hlt : t.1 < η' := lt_iff_le_not_ge.mpr ⟨hle, fun hge => hne'
      ((Scheme.le_iff_specializes.mp hge).antisymm (Scheme.le_iff_specializes.mp hle)).eq.symm⟩
    have hfin : Order.coheight η' < ⊤ := by
      have := Order.coheight_anti hle
      rw [t.2] at this
      exact lt_of_le_of_lt this (by norm_num)
    have hc := Order.coheight_strictAnti hlt hfin
    rw [t.2] at hc
    have h0 : Order.coheight η' = 0 := by
      have : Order.coheight η' < 1 := hc
      exact ENat.lt_one_iff_eq_zero.mp this
    have hmax : IsMax η' := Order.coheight_eq_zero.mp h0
    have hgle : η' ≤ genericPoint U := Scheme.le_iff_specializes.mpr (genericPoint_specializes η')
    have hgη : genericPoint U ≤ η' := hmax hgle
    have heqg : η' = genericPoint U :=
      ((Scheme.le_iff_specializes.mp hgη).antisymm (Scheme.le_iff_specializes.mp hgle)).eq
    exact hgenC (hFC (heqg ▸ hη'))
  exact ⟨e ⟨t.1, hgen, t.2⟩, by simp⟩

end MixedFujita
