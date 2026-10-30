/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentTotalTransform
public import MixedFujita.SNCCodimensionOneSupports

/-! Split the exceptional member of the actual SNC total transform according
to the components of the centre. Pointwise injective refinement preserves
SNC and compatibility with any subsequent centre. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem sncAt_of_pointwise_refinement
    {X : Scheme.{u}} (D F : DivisorFamily X) (φ : F.ι → D.ι)
    (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x)
    (hmem : ∀ i, x ∈ (F.component i).support → x ∈ (D.component (φ i)).support)
    (hst : ∀ i, x ∈ (F.component i).support →
      (F.component i).stalkIdeal x = (D.component (φ i)).stalkIdeal x)
    (hinj : ∀ i j, x ∈ (F.component i).support → x ∈ (F.component j).support →
      φ i = φ j → i = j) (hD : D.IsSncAt x z) : F.IsSncAt x z := by
  obtain ⟨hz, c, hc, hI⟩ := hD
  let e : {i : F.ι // x ∈ (F.component i).support} →
      {i : D.ι // x ∈ (D.component i).support} := fun i => ⟨φ i, hmem i i.2⟩
  refine ⟨hz, c ∘ e, ?_, ?_⟩
  · intro i j hij
    exact Subtype.ext (hinj i j i.2 j.2 (congrArg Subtype.val (hc hij)))
  · intro i
    exact (hst i i.2).trans (hI (e i))

theorem snc_of_pointwise_refinement
    {X : Scheme.{u}} (D F : DivisorFamily X) (φ : F.ι → D.ι)
    (hmem : ∀ i x, x ∈ (F.component i).support → x ∈ (D.component (φ i)).support)
    (hst : ∀ i x, x ∈ (F.component i).support →
      (F.component i).stalkIdeal x = (D.component (φ i)).stalkIdeal x)
    (hinj : ∀ x i j, x ∈ (F.component i).support → x ∈ (F.component j).support →
      φ i = φ j → i = j) (hD : D.IsSnc) : F.IsSnc := by
  refine ⟨?_, ?_⟩
  · intro i
    apply isRegular_subscheme_of_isRegularLocalRing_quotient
    intro x hx
    rw [hst i x hx]
    obtain ⟨w, hw⟩ := (D.component (φ i)).exists_subschemeι_eq (hmem i x hx)
    subst x
    let : IsRegularLocalRing ((D.component (φ i)).subscheme.presheaf.stalk w) :=
      (hD.1 (φ i)).1 w
    exact IsRegularLocalRing.of_ringEquiv ((D.component (φ i)).stalkQuotientEquiv w).symm
  · intro x
    obtain ⟨n, z, hz⟩ := hD.2 x
    exact ⟨n, z, sncAt_of_pointwise_refinement D F φ x z
      (fun i => hmem i x) (fun i => hst i x) (hinj x) hz⟩

theorem hasSncWith_of_pointwise_refinement
    {X : Scheme.{u}} (D F : DivisorFamily X) (φ : F.ι → D.ι)
    (hmem : ∀ i x, x ∈ (F.component i).support → x ∈ (D.component (φ i)).support)
    (hst : ∀ i x, x ∈ (F.component i).support →
      (F.component i).stalkIdeal x = (D.component (φ i)).stalkIdeal x)
    (hinj : ∀ x i j, x ∈ (F.component i).support → x ∈ (F.component j).support →
      φ i = φ j → i = j) (W : X.IdealSheafData) (hW : D.HasSncWith W) :
    F.HasSncWith W := by
  intro x hx
  obtain ⟨n, z, hz, s, hs⟩ := hW x hx
  exact ⟨n, z, sncAt_of_pointwise_refinement D F φ x z
    (fun i => hmem i x) (fun i => hst i x) (hinj x) hz, s, hs⟩

noncomputable def sncComponentTotalTransform
    {X : Scheme.{u}} [NoetherianSpace X] (D : DivisorFamily X) (Z : X.IdealSheafData) :
    DivisorFamily Z.blowUp where
  ι := D.ι ⊕ₗ Z.componentFamily.ι
  component := fun i => Sum.elim (fun a => (D.component a).strictTransform Z)
    (fun j => (Z.componentFamily.component j).comap Z.blowUpπ) (ofLex i)

noncomputable def sncComponentTotalTransformCollapse
    {X : Scheme.{u}} [NoetherianSpace X] (D : DivisorFamily X) (Z : X.IdealSheafData) :
    (sncComponentTotalTransform D Z).ι → (D.totalTransform Z).ι :=
  fun i => toLex (Sum.elim Sum.inl (fun _ => Sum.inr PUnit.unit) (ofLex i))

theorem sncComponentTotalTransform_refinement
    {X : Scheme.{u}} [NoetherianSpace X] (D : DivisorFamily X) (Z : X.IdealSheafData)
    (hZ : IsRegular Z.subscheme) :
    let F := sncComponentTotalTransform D Z
    let φ := sncComponentTotalTransformCollapse D Z
    (∀ i x, x ∈ (F.component i).support → x ∈ ((D.totalTransform Z).component (φ i)).support) ∧
    (∀ i x, x ∈ (F.component i).support →
      (F.component i).stalkIdeal x = ((D.totalTransform Z).component (φ i)).stalkIdeal x) ∧
    (∀ x i j, x ∈ (F.component i).support → x ∈ (F.component j).support →
      φ i = φ j → i = j) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i x hx
    rcases i with a | j
    · exact hx
    · exact (mem_support_comap_iff_apply Z Z.blowUpπ x).mpr
        (centre_component_support_subset Z j
          ((mem_support_comap_iff_apply _ Z.blowUpπ x).mp hx))
  · intro i x hx
    rcases i with a | j
    · rfl
    · change ((Z.componentFamily.component j).comap Z.blowUpπ).stalkIdeal x =
        (Z.comap Z.blowUpπ).stalkIdeal x
      rw [Scheme.IdealSheafData.stalkIdeal_comap, Scheme.IdealSheafData.stalkIdeal_comap,
        Hironaka.Sequence.stalkIdeal_componentFamily_eq Z hZ j
          ((mem_support_comap_iff_apply _ Z.blowUpπ x).mp hx)]
  · intro x i j hi hj hij
    rcases i with a | a <;> rcases j with b | b
    · change (Sum.inl a : D.ι ⊕ PUnit.{u + 1}) = Sum.inl b at hij
      have hab : a = b := Sum.inl.inj hij
      subst b
      rfl
    · change (Sum.inl a : D.ι ⊕ PUnit.{u + 1}) = Sum.inr PUnit.unit at hij
      cases hij
    · change (Sum.inr PUnit.unit : D.ι ⊕ PUnit.{u + 1}) = Sum.inl b at hij
      cases hij
    · have hab := Hironaka.Sequence.eq_of_mem_support_componentFamily Z hZ
        ((mem_support_comap_iff_apply _ Z.blowUpπ x).mp hi)
        ((mem_support_comap_iff_apply _ Z.blowUpπ x).mp hj)
      exact congrArg (fun a => toLex (Sum.inr a)) hab

theorem sncComponentTotalTransform_isSnc
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [NoetherianSpace X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (D : DivisorFamily X) (Z : X.IdealSheafData)
    (hD : D.IsSnc) (hZ : D.HasSncWith Z) : (sncComponentTotalTransform D Z).IsSnc := by
  obtain ⟨hm, hs, hi⟩ := sncComponentTotalTransform_refinement D Z (HasSncWith.isRegular f hZ)
  exact snc_of_pointwise_refinement (D.totalTransform Z) _ _ hm hs hi
    (totalTransform_isSnc f D Z hD hZ)

theorem sncComponentTotalTransform_hasSncWith
    {X : Scheme.{u}} [NoetherianSpace X] (D : DivisorFamily X) (Z : X.IdealSheafData)
    (hZ : IsRegular Z.subscheme) (W : Z.blowUp.IdealSheafData)
    (hW : (D.totalTransform Z).HasSncWith W) :
    (sncComponentTotalTransform D Z).HasSncWith W := by
  obtain ⟨hm, hs, hi⟩ := sncComponentTotalTransform_refinement D Z hZ
  exact hasSncWith_of_pointwise_refinement (D.totalTransform Z) _ _ hm hs hi W hW

end MixedFujita
