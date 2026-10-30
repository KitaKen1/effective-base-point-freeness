/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ComponentExceptionalCartier
public import MixedFujita.SNCConnectedCentreDimension
public import MixedFujita.SNCCentreIncidenceBound

/-! Intrinsic geometry of every component of a disconnected SNC centre.
Compatibility, integrality, incidence and positive codimension are derived
from the original centre. No connectedness or common centre dimension is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem centre_component_support_subset
    {X : Scheme.{u}} [NoetherianSpace X] (Z : X.IdealSheafData)
    (i : Z.componentFamily.ι) :
    (Z.componentFamily.component i).support ≤ Z.support := by
  intro x hx
  exact ((Hironaka.Sequence.mem_support_componentFamily_iff Z i x).mp hx).mem_closed
    Z.support.isClosed i.2.1

theorem sncCentre_component_hasSncWith
    {k : Type u} [Field k] {X : Scheme.{u}} [NoetherianSpace X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (i : Z.componentFamily.ι) : D.HasSncWith (Z.componentFamily.component i) := by
  intro x hx
  obtain ⟨n, z, hz, s, hs⟩ := hZ x (centre_component_support_subset Z i hx)
  exact ⟨n, z, hz, s, (Hironaka.Sequence.stalkIdeal_componentFamily_eq Z
    (HasSncWith.isRegular f hZ) i hx).trans hs⟩

theorem sncCentre_component_isIntegral
    {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (i : Z.componentFamily.ι) : IsIntegral (Z.componentFamily.component i).subscheme := by
  let := Hironaka.Sequence.irreducibleSpace_subscheme_componentFamily Z i
  let := LocallyOfFiniteType.isLocallyNoetherian (Z.componentFamily.component i).subschemeι
  let : NoetherianSpace (Z.componentFamily.component i).subscheme :=
    (Z.componentFamily.component i).subschemeι.isClosedEmbedding.isInducing.noetherianSpace
  let : IsNoetherian (Z.componentFamily.component i).subscheme := {}
  exact snc_connectedCentre_isIntegral f D _ (sncCentre_component_hasSncWith f D Z hZ i)

theorem sncCentre_component_incidence_iff
    {k : Type u} [Field k] {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) [Smooth f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (i : Z.componentFamily.ι) (P : X.IdealSheafData) (x : X)
    (hx : x ∈ (Z.componentFamily.component i).support) :
    P.stalkIdeal x ≤ Z.stalkIdeal x ↔ P ≤ Z.componentFamily.component i := by
  let := sncCentre_component_isIntegral f D Z hZ i
  rw [← Hironaka.Sequence.stalkIdeal_componentFamily_eq Z (HasSncWith.isRegular f hZ) i hx]
  exact integralSubscheme_stalkIdeal_le_iff P _ x hx

/-- The codimension and the incidence bound are constructed separately for
each centre component; different components may have different codimensions. -/
theorem sncCentre_exists_component_codimensions
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support) :
    ∃ c : Z.componentFamily.ι → ℕ, ∀ i,
      0 < c i ∧ c i ≤ n ∧
      SmoothOfRelativeDimension (n - c i) ((Z.componentFamily.component i).subschemeι ≫ f) ∧
      topologicalKrullDim (Z.componentFamily.component i).subscheme = n - c i ∧
      ∀ s : Finset D.ι, (∀ j ∈ s, D.component j ≤ Z.componentFamily.component i) →
        s.card ≤ c i := by
  classical
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  have hex (i : Z.componentFamily.ι) : ∃ c : ℕ, 0 < c ∧ c ≤ n ∧
      SmoothOfRelativeDimension (n - c) ((Z.componentFamily.component i).subschemeι ≫ f) ∧
      topologicalKrullDim (Z.componentFamily.component i).subscheme = n - c := by
    let := sncCentre_component_isIntegral f D Z hZ i
    let := LocallyOfFiniteType.isLocallyNoetherian (Z.componentFamily.component i).subschemeι
    let : NoetherianSpace (Z.componentFamily.component i).subscheme :=
      (Z.componentFamily.component i).subschemeι.isClosedEmbedding.isInducing.noetherianSpace
    let : IsNoetherian (Z.componentFamily.component i).subscheme := {}
    exact snc_connectedCentre_exists_codimension_of_relativeDimension f n D _
      (sncCentre_component_hasSncWith f D Z hZ i)
      (fun h => hη (centre_component_support_subset Z i h))
  choose c hc hcn hdim htop using hex
  refine ⟨c, fun i => ⟨hc i, hcn i, hdim i, htop i, ?_⟩⟩
  let := hdim i
  let := sncCentre_component_isIntegral f D Z hZ i
  exact fun s hs => snc_containing_components_card_le_codimension f n (c i) D _
    (sncCentre_component_hasSncWith f D Z hZ i) (hcn i) s hs

end MixedFujita
