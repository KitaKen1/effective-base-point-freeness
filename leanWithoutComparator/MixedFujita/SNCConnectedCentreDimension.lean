/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ConnectedRegularCentre
public import MixedFujita.EtaleChartDimension
public import Hironaka.Scheme.Snc.RelativeDimensionConstant

/-! Derive fixed positive relative codimension from the original connected SNC
center hypotheses. The only dimension comparison is topological: a chain in a
proper closed subspace extends by the ambient irreducible closed space. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem properClosedImmersion_finite_dimensions_lt
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (i : Y ⟶ X) [IsClosedImmersion i] (hproper : Set.range i ≠ Set.univ)
    (n m : ℕ) (hX : topologicalKrullDim X = n) (hY : topologicalKrullDim Y = m) : m < n := by
  let F := IrreducibleCloseds.map (fun y : Y => i y) i.continuous
  have hF : StrictMono F :=
    IrreducibleCloseds.map_strictMono_of_isInducing i.isClosedEmbedding.isInducing
  let whole : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlt (C : IrreducibleCloseds Y) : F C < whole := by
    have hsub : (F C : Set X) ⊆ Set.range i := by
      change closure (i '' (C : Set Y)) ⊆ _
      rw [(i.isClosedMap _ C.isClosed).closure_eq]
      exact Set.image_subset_range _ _
    refine lt_iff_le_not_ge.mpr ⟨Set.subset_univ _, fun h => hproper ?_⟩
    exact Set.eq_univ_of_univ_subset (Set.Subset.trans h hsub)
  let : Nonempty (IrreducibleCloseds Y) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩⟩
  have h := Order.krullDim_le_of_strictMono _
    (WithTop.strictMono_iff.mpr ⟨hF, hlt⟩ : StrictMono (WithTop.recTopCoe whole F))
  rw [Order.krullDim_WithTop] at h
  change topologicalKrullDim Y + 1 ≤ topologicalKrullDim X at h
  rw [hX, hY] at h
  have hmn : m + 1 ≤ n := by exact_mod_cast h
  omega

theorem irreducible_smooth_relativeDimension_eq_dimension
    {K : Type u} [Field K] {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f] :
    topologicalKrullDim X = n := by
  let : X.Over (Spec (.of K)) := ⟨f⟩
  let : SmoothOfRelativeDimension n (X ↘ Spec (.of K)) := ‹SmoothOfRelativeDimension n f›
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  have hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤ := etaleCharts_cover
  let x : X := Classical.arbitrary X
  obtain ⟨c, _⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
  exact etaleChart_topologicalKrullDim c

theorem snc_connectedCentre_exists_positive_relative_codimension
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] [ConnectedSpace Z.subscheme]
    (hη : genericPoint X ∉ Z.support) :
    ∃ n c : ℕ, 0 < c ∧ c ≤ n ∧ SmoothOfRelativeDimension n f ∧
      SmoothOfRelativeDimension (n - c) (Z.subschemeι ≫ f) ∧
      topologicalKrullDim X = n ∧ topologicalKrullDim Z.subscheme = n - c := by
  let := snc_connectedCentre_isIntegral f D Z hZ
  let := HasSncWith.smooth f hZ
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension_of_preconnectedSpace f
  obtain ⟨m, hm⟩ := exists_smoothOfRelativeDimension_of_preconnectedSpace (Z.subschemeι ≫ f)
  let := hn
  let := hm
  have hX := irreducible_smooth_relativeDimension_eq_dimension f n
  have hZdim := irreducible_smooth_relativeDimension_eq_dimension (Z.subschemeι ≫ f) m
  have hproper : Set.range Z.subschemeι ≠ Set.univ := by
    rw [Z.range_subschemeι]
    intro h
    apply hη
    change genericPoint X ∈ (Z.support : Set X)
    rw [h]
    trivial
  have hmn := properClosedImmersion_finite_dimensions_lt Z.subschemeι hproper n m hX hZdim
  have hsub : n - (n - m) = m := by omega
  refine ⟨n, n - m, by omega, Nat.sub_le _ _, hn, ?_, hX, ?_⟩
  · simpa only [hsub] using hm
  · simpa only [hsub] using hZdim

theorem snc_connectedCentre_exists_codimension_of_relativeDimension
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (D : Scheme.DivisorFamily X) (Z : X.IdealSheafData) (hZ : D.HasSncWith Z)
    [IsNoetherian Z.subscheme] [ConnectedSpace Z.subscheme]
    (hη : genericPoint X ∉ Z.support) :
    ∃ c : ℕ, 0 < c ∧ c ≤ n ∧ SmoothOfRelativeDimension (n - c) (Z.subschemeι ≫ f) ∧
      topologicalKrullDim Z.subscheme = n - c := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨n', c, hc, hcn, _, hdim, hX, hZdim⟩ :=
    snc_connectedCentre_exists_positive_relative_codimension f D Z hZ hη
  have hnn : n' = n := by
    have h := hX.symm.trans (irreducible_smooth_relativeDimension_eq_dimension f n)
    exact_mod_cast h
  subst n'
  exact ⟨c, hc, hcn, hdim, hZdim⟩

end MixedFujita
