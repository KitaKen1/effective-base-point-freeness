/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCComponentTransformFamily
public import Hironaka.Scheme.BlowUpSequence.InducedData

/-! Pointwise boundary refinement survives strict and total transforms.
Consequently a standard Hironaka order sequence remains an order sequence after
splitting boundary members into disjoint local pieces. No additional centre
compatibility is required on the refined sequence. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

/-- Each refined member agrees locally with its image wherever it is present;
no two refined members over the same member meet. Surjectivity is not needed. -/
def sncFamilyRefines {X : Scheme.{u}} (F D : DivisorFamily X) : Prop :=
  ∃ φ : F.ι → D.ι,
    (∀ i x, x ∈ (F.component i).support → x ∈ (D.component (φ i)).support) ∧
    (∀ i x, x ∈ (F.component i).support →
      (F.component i).stalkIdeal x = (D.component (φ i)).stalkIdeal x) ∧
    (∀ x i j, x ∈ (F.component i).support → x ∈ (F.component j).support →
      φ i = φ j → i = j)

theorem sncFamilyRefines_refl {X : Scheme.{u}} (D : DivisorFamily X) :
    sncFamilyRefines D D :=
  ⟨id, fun _ _ h => h, fun _ _ _ => rfl, fun _ _ _ _ _ h => h⟩

theorem sncFamilyRefines_trans {X : Scheme.{u}} {F D G : DivisorFamily X}
    (hFD : sncFamilyRefines F D) (hDG : sncFamilyRefines D G) : sncFamilyRefines F G := by
  obtain ⟨φ, hm, hs, hi⟩ := hFD
  obtain ⟨ψ, hm', hs', hi'⟩ := hDG
  exact ⟨ψ ∘ φ, fun i x h => hm' _ _ (hm i x h),
    fun i x h => (hs i x h).trans (hs' _ _ (hm i x h)),
    fun x i j hix hjx h => hi x i j hix hjx (hi' x _ _ (hm i x hix) (hm j x hjx) h)⟩

theorem sncFamilyRefines_isSnc {X : Scheme.{u}} {F D : DivisorFamily X}
    (h : sncFamilyRefines F D) (hD : D.IsSnc) : F.IsSnc := by
  obtain ⟨φ, hm, hs, hi⟩ := h
  exact snc_of_pointwise_refinement D F φ hm hs hi hD

theorem sncFamilyRefines_hasSncWith {X : Scheme.{u}} {F D : DivisorFamily X}
    (h : sncFamilyRefines F D) {Z : X.IdealSheafData} (hZ : D.HasSncWith Z) :
    F.HasSncWith Z := by
  obtain ⟨φ, hm, hs, hi⟩ := h
  exact hasSncWith_of_pointwise_refinement D F φ hm hs hi Z hZ

/-- Saturation commutes with equality of the original stalk ideals. -/
theorem strictTransform_stalkIdeal_eq_of_stalkIdeal_eq
    {X : Scheme.{u}} (Z I J : X.IdealSheafData) (y : Z.blowUp)
    (h : I.stalkIdeal (Z.blowUpπ y) = J.stalkIdeal (Z.blowUpπ y)) :
    (I.strictTransform Z).stalkIdeal y = (J.strictTransform Z).stalkIdeal y := by
  change (I.strictTransformAlong Z.blowUpπ (Z.comap Z.blowUpπ)).stalkIdeal y =
    (J.strictTransformAlong Z.blowUpπ (Z.comap Z.blowUpπ)).stalkIdeal y
  rw [stalkIdeal_strictTransformAlong_eq_iSup, stalkIdeal_strictTransformAlong_eq_iSup]
  simp only [Scheme.IdealSheafData.stalkIdeal_comap, h]

theorem sncFamilyRefines_totalTransform {X : Scheme.{u}} {F D : DivisorFamily X}
    (h : sncFamilyRefines F D) (Z : X.IdealSheafData) :
    sncFamilyRefines (F.totalTransform Z) (D.totalTransform Z) := by
  obtain ⟨φ, hm, hs, hi⟩ := h
  let φ' : (F.totalTransform Z).ι → (D.totalTransform Z).ι :=
    fun i => toLex (Sum.map φ id (ofLex i))
  have hst (i : F.ι) (y : Z.blowUp)
      (hy : y ∈ ((F.component i).strictTransform Z).support) :
      ((F.component i).strictTransform Z).stalkIdeal y =
        ((D.component (φ i)).strictTransform Z).stalkIdeal y :=
    strictTransform_stalkIdeal_eq_of_stalkIdeal_eq Z _ _ y
      (hs i _ (π_mem_support_of_mem_support_strictTransformAlong Z (F.component i) y hy))
  refine ⟨φ', ?_, ?_, ?_⟩
  · intro i y hy
    rcases i with i | j
    · change y ∈ ((D.component (φ i)).strictTransform Z).support
      rw [Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal,
        ← hst i y hy]
      exact (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp hy
    · exact hy
  · intro i y hy
    rcases i with i | j
    · exact hst i y hy
    · rfl
  · intro y i j hiy hjy hij
    rcases i with i | i <;> rcases j with j | j
    · have hij' : φ i = φ j := Sum.inl.inj (toLex.injective hij)
      have h := hi (Z.blowUpπ y) i j
        (π_mem_support_of_mem_support_strictTransformAlong Z (F.component i) y hiy)
        (π_mem_support_of_mem_support_strictTransformAlong Z (F.component j) y hjy) hij'
      exact congrArg (fun a => toLex (Sum.inl a)) h
    · change (Sum.inl (φ i) : D.ι ⊕ PUnit.{u + 1}) = Sum.inr j at hij
      cases hij
    · change (Sum.inr i : D.ι ⊕ PUnit.{u + 1}) = Sum.inl (φ j) at hij
      cases hij
    · exact congrArg (fun a => toLex (Sum.inr a)) (Subsingleton.elim i j)

theorem sncComponentTotalTransform_refines_totalTransform
    {X : Scheme.{u}} [NoetherianSpace X] (D : DivisorFamily X) (Z : X.IdealSheafData)
    (hZ : IsRegular Z.subscheme) :
    sncFamilyRefines (sncComponentTotalTransform D Z) (D.totalTransform Z) :=
  ⟨sncComponentTotalTransformCollapse D Z, sncComponentTotalTransform_refinement D Z hZ⟩

/-- Refinement transports all the centre-compatibility conditions of an actual
Hironaka sequence, including the recursively transformed boundaries. -/
theorem sncFamilyRefines_isOrderSeq {k : Type u} [Field k] {X : Scheme.{u}}
    {S : BlowUpSequence X} {F D : DivisorFamily X} (href : sncFamilyRefines F D)
    {f : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ}
    (hS : S.IsOrderSeq f I D m) : S.IsOrderSeq f I F m := by
  induction S with
  | nil X => exact ⟨hS.1, fun i => i.elim0⟩
  | cons X Z rest ih =>
    rw [isOrderSeq_cons_iff] at hS ⊢
    exact ⟨⟨hS.1.1, sncFamilyRefines_hasSncWith href hS.1.2.1, hS.1.2.2⟩,
      ih (sncFamilyRefines_totalTransform href Z) hS.2⟩

theorem sncFamilyRefines_isOrderGeSeq {k : Type u} [Field k] {X : Scheme.{u}}
    {S : BlowUpSequence X} {F D : DivisorFamily X} (href : sncFamilyRefines F D)
    {f : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {m : ℕ}
    (hS : S.IsOrderGeSeq f I m D) : S.IsOrderGeSeq f I m F := by
  induction S with
  | nil X => exact ⟨hS.1, fun i => i.elim0⟩
  | cons X Z rest ih =>
    rw [isOrderGeSeq_cons_iff] at hS ⊢
    exact ⟨⟨hS.1.1, sncFamilyRefines_hasSncWith href hS.1.2.1, hS.1.2.2⟩,
      ih (sncFamilyRefines_totalTransform href Z) hS.2⟩

end MixedFujita
