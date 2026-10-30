/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCConnectedCentreDimension
public import Hironaka.Scheme.Smooth.AdaptedCoordinates

/-! At most c SNC components contain a smooth center of codimension c.
At one closed point, the component labels inject into the normal parameters;
the quotient stalk dimension identifies their number with c. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
theorem snc_containing_components_card_le_codimension
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) (n c : ℕ) [SmoothOfRelativeDimension n f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsIntegral Z.subscheme] [SmoothOfRelativeDimension (n - c) (Z.subschemeι ≫ f)]
    (hcn : c ≤ n) (s : Finset D.ι) (hcontains : ∀ i ∈ s, D.component i ≤ Z) : s.card ≤ c := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : Smooth (Z.subschemeι ≫ f) := SmoothOfRelativeDimension.smooth (n - c) _
  let : JacobsonSpace Z.subscheme := LocallyOfFiniteType.jacobsonSpace (Z.subschemeι ≫ f)
  obtain ⟨w, _, hw⟩ := nonempty_inter_closedPoints (X := Z.subscheme)
    (Z := Set.univ) Set.univ_nonempty isClosed_univ.isLocallyClosed
  have hx : IsClosed ({Z.subschemeι w} : Set X) := by
    simpa only [Set.image_singleton] using Z.subschemeι.isClosedMap _ hw
  have hwZ : Z.subschemeι w ∈ Z.support := subschemeι_mem_support Z w
  obtain ⟨N, z, hz, t, ht⟩ := hZ _ hwZ
  let := isRegularLocalRing_stalk f (Z.subschemeι w)
  have hN : N = n := by
    have h := hz.1.2.trans
      ((TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed f hx).trans
        (irreducible_smooth_relativeDimension_eq_dimension f n))
    exact_mod_cast h
  have hQ := natCast_sub_card_eq_ringKrullDim_stalk_subscheme Z w hz.1 ht
  rw [TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
    (Z.subschemeι ≫ f) hw, irreducible_smooth_relativeDimension_eq_dimension (Z.subschemeι ≫ f) (n - c)] at hQ
  have hQnat : N - t.card = n - c := by exact_mod_cast hQ
  have htN : t.card ≤ N := by simpa using t.card_le_univ
  have htc : t.card = c := by omega
  obtain ⟨a, ha, hcoord⟩ := hz.2
  let pointLabel (i : s) : {i : D.ι // Z.subschemeι w ∈ (D.component i).support} :=
    ⟨i, Scheme.IdealSheafData.support_antitone (hcontains i i.2) hwZ⟩
  let e : s → t := fun i => ⟨a (pointLabel i),
    (IsSncAt.stalkIdeal_le_iff_mem f hz ht (hcoord (pointLabel i))).mp
      (Scheme.IdealSheafData.stalkIdeal_mono (hcontains i i.2) _)⟩
  have he : Function.Injective e := by
    intro i j hij
    have h : a (pointLabel i) = a (pointLabel j) := congrArg Subtype.val hij
    apply Subtype.ext
    exact congrArg (fun j : {i : D.ι // Z.subschemeι w ∈ (D.component i).support} => j.val) (ha h)
  simpa only [htc] using Finset.card_le_card_of_injective he

theorem snc_containing_component_filter_card_le
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) (n c : ℕ) [SmoothOfRelativeDimension n f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsIntegral Z.subscheme] [SmoothOfRelativeDimension (n - c) (Z.subschemeι ≫ f)]
    (hcn : c ≤ n) [Fintype D.ι] :
    (Finset.univ.filter (fun i => D.component i ≤ Z)).card ≤ c :=
  snc_containing_components_card_le_codimension f n c D Z hZ hcn _
    (fun _ hi => (Finset.mem_filter.mp hi).2)

end MixedFujita
