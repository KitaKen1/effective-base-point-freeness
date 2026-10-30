/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentCentreData
public import MixedFujita.ComponentExceptionalLocalization
public import Hironaka.Scheme.Smooth.ExceptionalBundle
public import Hironaka.Scheme.Smooth.EtaleCoordinates
public import Hironaka.Scheme.Smooth.BlowUpSmooth
public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Collapse

/-! Adapted coordinates for the original disconnected centre, with the
codimension of the component through the chosen point. The chart is shrunk
inside its component-isolating open, keeping the original ambient scheme. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem adaptedCoordinates_exists_restrict_of_comap_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {n r : ℕ} {I Z : X.IdealSheafData} {x y : X}
    (E : EtaleCoordinatesAdapted f n r I y) (V : X.affineOpens)
    (hx : x ∈ V.1) (hVE : V.1 ≤ E.U.1) (hIZ : Z.comap V.1.ι = I.comap V.1.ι) :
    ∃ E' : EtaleCoordinatesAdapted f n r Z x, E'.U = V := by
  let : Etale (toAffineSpace f E.U.1 E.v) := E.etale
  refine ⟨⟨V, hx, fun j => X.presheaf.map (homOfLE hVE).op (E.v j),
    etale_toAffineSpace_restrict f hVE E.v, ?_⟩, rfl⟩
  rw [hIZ, ← X.homOfLE_ι hVE, Scheme.IdealSheafData.comap_comp, E.adapted,
    ← Scheme.IdealSheafData.comap_comp, homOfLE_toAffineSpace]

theorem sncCentre_component_exists_adapted_coordinates
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) (n r : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (i : Z.componentFamily.ι)
    [SmoothOfRelativeDimension (n - r) ((Z.componentFamily.component i).subschemeι ≫ f)]
    (hrn : r ≤ n) (x : X) (hx : x ∈ (Z.componentFamily.component i).support) :
    Nonempty (EtaleCoordinatesAdapted f n r Z x) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨U, hU, _, hZI⟩ := regularCentre_exists_component_isolating_open Z
    (HasSncWith.isRegular f hZ) i
  obtain ⟨z, hz⟩ := (Z.componentFamily.component i).exists_subschemeι_eq hx
  obtain ⟨a, ha⟩ := exists_adaptedChart_mem f n r (Z.componentFamily.component i) hrn z
  let E := adaptedChart f n r (Z.componentFamily.component i) hrn a
  have hxE : x ∈ E.U.1 := hz ▸ ha
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ E.U.1 ⊓ U from ⟨hxE, hU hx⟩)
      (E.U.1 ⊓ U).isOpen
  let V : X.affineOpens := ⟨W, hW⟩
  have hVE : V.1 ≤ E.U.1 := fun _ h => (hWsub h).1
  have hVU : V.1 ≤ U := fun _ h => (hWsub h).2
  have hIZ : Z.comap V.1.ι = (Z.componentFamily.component i).comap V.1.ι := by
    rw [← X.homOfLE_ι hVU, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, hZI]
  obtain ⟨E', _⟩ := adaptedCoordinates_exists_restrict_of_comap_eq f E V hxW hVE hIZ
  exact ⟨E'⟩

theorem regularCentre_exists_component_through
    {X : Scheme.{u}} [NoetherianSpace X] (Z : X.IdealSheafData)
    (hZ : IsRegular Z.subscheme) (x : X) (hx : x ∈ Z.support) :
    ∃ i : Z.componentFamily.ι, x ∈ (Z.componentFamily.component i).support := by
  rw [← Hironaka.Sequence.prod_componentFamily_eq Z hZ] at hx
  obtain ⟨i, _, hi⟩ := (Hironaka.Sequence.mem_support_finset_prod_iff _ _ x).mp hx
  exact ⟨i, hi⟩

/-- The local codimension may vary: every adapted chart still has ambient
relative dimension n, so these charts glue to smoothness of that dimension. -/
theorem blowUp_smoothOfRelativeDimension_of_adapted_coordinates
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (Z : X.IdealSheafData)
    (hcoords : ∀ x : X, x ∈ Z.support → ∃ r : ℕ, Nonempty (EtaleCoordinatesAdapted f n r Z x)) :
    SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) := by
  classical
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  choose r hE using fun x : {x : X // x ∈ Z.support} => hcoords x.1 x.2
  let E := fun x => Classical.choice (hE x)
  let V : Option {x : X // x ∈ Z.support} → X.Opens :=
    fun o => o.elim Z.support.compl fun x => (E x).U.1
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro x _
    by_cases hx : x ∈ Z.support
    · exact Opens.mem_iSup.mpr ⟨some ⟨x, hx⟩, (E ⟨x, hx⟩).mem⟩
    · exact Opens.mem_iSup.mpr ⟨none, hx⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} n)
    (fun o => Z.blowUpπ ⁻¹ᵁ V o) ?_ fun o => ?_
  · rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]
  · rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    cases o with
    | none => exact smoothOfRelativeDimension_restrict_compl_support f n Z
    | some x => exact smoothOfRelativeDimension_restrict_of_etaleCoordinates (E x)

theorem snc_disconnectedCentre_blowUp_smoothOfRelativeDimension
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian X]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    (hη : genericPoint X ∉ Z.support) : SmoothOfRelativeDimension n (Z.blowUpπ ≫ f) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨c, hc⟩ := sncCentre_exists_component_codimensions f n D Z hZ hη
  apply blowUp_smoothOfRelativeDimension_of_adapted_coordinates f n Z
  intro x hx
  obtain ⟨i, hi⟩ := regularCentre_exists_component_through Z (HasSncWith.isRegular f hZ) x hx
  let := (hc i).2.2.1
  exact ⟨c i, sncCentre_component_exists_adapted_coordinates f n (c i) D Z hZ i (hc i).2.1 x hi⟩

end MixedFujita
