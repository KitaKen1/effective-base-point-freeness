/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TransverseParameterExtension
public import MixedFujita.SNCStrataGenericSmoothness
public import Hironaka.Scheme.Snc.Basic

/-!
Append an actual principal transverse cut to an SNC family. The transverse
condition uses the actual closed intersection of the components through each
point, not an externally supplied coordinate system. Extend parameters while
retaining the original component equations and prove regularity of the new
closed divisor internally.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The actual closed intersection of all boundary components passing through the point. -/
noncomputable def sncActiveStratumIdeal {X : Scheme.{u}} (E : Scheme.DivisorFamily X)
    (x : X) : X.IdealSheafData := by
  classical
  exact sncStratumIdeal E (Finset.univ.filter fun i => x ∈ (E.component i).support)

/-- The active closed stratum has exactly the span of the active coordinate equations as its stalk. -/
theorem sncActiveStratumIdeal_stalk_eq_span {X : Scheme.{u}}
    (E : Scheme.DivisorFamily X) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x)
    (c : {i : E.ι // x ∈ (E.component i).support} → Fin n)
    (hc : ∀ i, (E.component i.1).stalkIdeal x = Ideal.span {z (c i)}) :
    (sncActiveStratumIdeal E x).stalkIdeal x = Ideal.span (Set.range fun i => z (c i)) := by
  classical
  apply le_antisymm
  · rw [sncActiveStratumIdeal, sncStratumIdeal, Scheme.IdealSheafData.stalkIdeal_iSup']
    apply iSup_le
    intro i
    rw [Scheme.IdealSheafData.stalkIdeal_iSup']
    apply iSup_le
    intro hi
    have hix : x ∈ (E.component i).support := (Finset.mem_filter.mp hi).2
    rw [hc ⟨i, hix⟩]
    apply Ideal.span_le.mpr
    rintro a rfl
    exact Ideal.subset_span ⟨⟨i, hix⟩, rfl⟩
  · apply Ideal.span_le.mpr
    rintro a ⟨i, rfl⟩
    have hle : (E.component i.1).stalkIdeal x ≤ (sncActiveStratumIdeal E x).stalkIdeal x := by
      rw [sncActiveStratumIdeal, sncStratumIdeal, Scheme.IdealSheafData.stalkIdeal_iSup']
      apply le_iSup_of_le i.1
      rw [Scheme.IdealSheafData.stalkIdeal_iSup']
      exact le_iSup_of_le (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.2) le_rfl
    apply hle
    rw [hc i]
    exact Ideal.subset_span (Set.mem_singleton _)

/-- A principal cut transverse to the active closed stratum extends the actual SNC parameter data. -/
theorem exists_isSncAt_append_of_transverse_principal_cut {X : Scheme.{u}}
    (E : Scheme.DivisorFamily X) (H : X.IdealSheafData) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)]
    (hE : ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), E.IsSncAt x z)
    (hH : x ∈ H.support → ∃ a : X.presheaf.stalk x,
      H.stalkIdeal x = Ideal.span {a} ∧ a ∈ maximalIdeal (X.presheaf.stalk x) ∧
        a ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ (sncActiveStratumIdeal E x).stalkIdeal x) :
    ∃ (m : ℕ) (y : Fin m → X.presheaf.stalk x), (E.append H).IsSncAt x y := by
  classical
  obtain ⟨n, z, hz, c, hcinj, hc⟩ := hE
  by_cases hxH : x ∈ H.support
  · obtain ⟨a, hHa, ha, htrans⟩ := hH hxH
    rw [sncActiveStratumIdeal_stalk_eq_span E x z c hc] at htrans
    obtain ⟨m, y, hy, τ, hτ, hnew, hold⟩ :=
      exists_regular_parameters_with_transverse_element z hz c hcinj a ha htrans
    let index : {i : (E.append H).ι // x ∈ ((E.append H).component i).support} →
        Option {i : E.ι // x ∈ (E.component i).support} := fun i =>
      Sum.rec
        (motive := fun s => x ∈ ((E.append H).component (toLex s)).support →
          Option {i : E.ι // x ∈ (E.component i).support})
        (fun j hj => some ⟨j, hj⟩) (fun _ _ => none) (ofLex i.1) i.2
    refine ⟨m, y, hy, fun i => τ (index i), ?_, ?_⟩
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have h := hτ hij
      rcases i with a | u <;> rcases j with b | v
      · change (some ⟨a, hi⟩ : Option {i : E.ι // x ∈ (E.component i).support}) =
          some ⟨b, hj⟩ at h
        have hab : a = b := congrArg Subtype.val (Option.some.inj h)
        subst b
        rfl
      · change (some ⟨a, hi⟩ : Option {i : E.ι // x ∈ (E.component i).support}) = none at h
        cases h
      · change none = (some ⟨b, hj⟩ : Option {i : E.ι // x ∈ (E.component i).support}) at h
        cases h
      · cases u; cases v; rfl
    · rintro ⟨i, hi⟩
      rcases i with j | u
      · change (E.component j).stalkIdeal x = Ideal.span {y (τ (some ⟨j, hi⟩))}
        rw [hold]
        exact hc ⟨j, hi⟩
      · change H.stalkIdeal x = Ideal.span {y (τ none)}
        rw [hnew]
        exact hHa
  · let index : {i : (E.append H).ι // x ∈ ((E.append H).component i).support} →
        {i : E.ι // x ∈ (E.component i).support} := fun i =>
      Sum.rec
        (motive := fun s => x ∈ ((E.append H).component (toLex s)).support →
          {i : E.ι // x ∈ (E.component i).support})
        (fun j hj => ⟨j, hj⟩) (fun _ hu => (hxH hu).elim) (ofLex i.1) i.2
    refine ⟨n, z, hz, fun i => c (index i), ?_, ?_⟩
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      rcases i with a | u <;> rcases j with b | v
      · change c ⟨a, hi⟩ = c ⟨b, hj⟩ at hij
        have hab : a = b := congrArg Subtype.val (hcinj hij)
        subst b
        rfl
      · exact (hxH hj).elim
      · exact (hxH hi).elim
      · exact (hxH hi).elim
    · rintro ⟨i, hi⟩
      rcases i with j | u
      · exact hc ⟨j, hi⟩
      · exact (hxH hi).elim

/-- Appending an actual transverse principal cut preserves SNC, including regularity of its closed scheme. -/
theorem isSnc_append_of_transverse_principal_cut {X : Scheme.{u}}
    (E : Scheme.DivisorFamily X) (H : X.IdealSheafData) (hE : E.IsSnc)
    (hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    (hH : ∀ x ∈ H.support, ∃ a : X.presheaf.stalk x,
      H.stalkIdeal x = Ideal.span {a} ∧ a ∈ maximalIdeal (X.presheaf.stalk x) ∧
        a ∉ maximalIdeal (X.presheaf.stalk x) ^ 2 ⊔ (sncActiveStratumIdeal E x).stalkIdeal x) :
    (E.append H).IsSnc := by
  have hlocal (x : X) : ∃ (m : ℕ) (y : Fin m → X.presheaf.stalk x),
      (E.append H).IsSncAt x y := by
    letI := hreg x
    exact exists_isSncAt_append_of_transverse_principal_cut E H x (hE.2 x) (hH x)
  refine ⟨?_, hlocal⟩
  intro i
  obtain ⟨i, rfl⟩ := toLex.surjective i
  cases i with
  | inl i => exact hE.1 i
  | inr i =>
    apply isRegular_subscheme_of_isRegularLocalRing_quotient H
    intro x hx
    letI := hreg x
    obtain ⟨m, y, hy, c, hcinj, hc⟩ := hlocal x
    have hHa : H.stalkIdeal x = Ideal.span {y (c ⟨toLex (Sum.inr i), hx⟩)} := hc ⟨toLex (Sum.inr i), hx⟩
    exact isRegularLocalRing_quotient_stalkIdeal_of_eq_span
      (s := {c ⟨toLex (Sum.inr i), hx⟩}) hy
      (by simpa only [Finset.coe_singleton, Set.image_singleton] using hHa)

end MixedFujita
