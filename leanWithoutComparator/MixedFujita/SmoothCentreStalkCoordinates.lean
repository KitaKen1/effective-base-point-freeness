/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineIdealSheaves
public import Hironaka.Scheme.Smooth.ExceptionalBundle
public import Hironaka.Scheme.Smooth.LocalBlowUp
public import Hironaka.Scheme.Smooth.SubschemeStalk
public import Hironaka.Scheme.IdealSheaf.Order.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Flat coordinate maps at every point of a smooth center. The coordinates
come from an adapted etale neighborhood covering the point; full faithfulness
of Spec recovers the ring map without rebuilding the coordinate algebra. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme
open CoordinateSubspace
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem flat_nonempty_isDominant {X Y : Scheme.{u}} [Nonempty X] [IsIntegral Y]
    (f : X ⟶ Y) [Flat f] : IsDominant f := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨z, _, hz⟩ := Flat.generalizingMap f
    (show genericPoint Y ⤳ f x from (genericPoint_spec Y).specializes trivial)
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff]
  have h : ({genericPoint Y} : Set Y) ⊆ Set.range f := by
    rintro y rfl
    exact ⟨z, hz⟩
  simpa only [(genericPoint_spec Y).def] using closure_mono h

theorem etaleAdapted_exists_flat_stalk_coordinates
    {K : Type u} [Field K] {X : Scheme.{u}} {f : X ⟶ Spec (.of K)}
    {n c : ℕ} {Z : X.IdealSheafData} {x : X}
    (E : EtaleCoordinatesAdapted f n c Z x) (y : X) (hy : y ∈ E.U.1) :
    ∃ φ : MvPolynomial (Fin n) K →+* X.presheaf.stalk y, φ.Flat ∧
      Z.comap (X.fromSpecStalk y) = specIdealSheaf ((centerIdeal K n c).map φ) := by
  let σ := E.U.1.fromSpecStalkOfMem y hy
  let g := toAffineSpace f E.U.1 E.v
  let φ := (Spec.preimage (σ ≫ g)).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = σ ≫ g := Spec.map_preimage _
  let : Etale g := E.etale
  have : Flat σ := by
    dsimp only [σ, Scheme.Opens.fromSpecStalkOfMem]
    let := flat_fromSpecStalk (X := E.U.1.toScheme) ⟨y, hy⟩
    infer_instance
  refine ⟨φ, ?_, ?_⟩
  · apply Flat.SpecMap_iff.mp
    rw [Spec.map_preimage]
    infer_instance
  · calc
      Z.comap (X.fromSpecStalk y) = (Z.comap E.U.1.ι).comap σ := by
        rw [← Scheme.IdealSheafData.comap_comp, Scheme.Opens.fromSpecStalkOfMem_ι]
      _ = (specIdealSheaf (centerIdeal K n c)).comap (σ ≫ g) := by
        rw [E.adapted, Scheme.IdealSheafData.comap_comp]
        rfl
      _ = specIdealSheaf ((centerIdeal K n c).map φ) := by
        rw [← hφ, specIdealSheaf_comap]

theorem smoothCentre_exists_flat_stalk_coordinates
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n c : ℕ) [SmoothOfRelativeDimension n f]
    (Z : X.IdealSheafData) [SmoothOfRelativeDimension (n - c) (Z.subschemeι ≫ f)]
    (hcn : c ≤ n) (x : X) (hx : x ∈ Z.support) :
    ∃ φ : MvPolynomial (Fin n) K →+* X.presheaf.stalk x, φ.Flat ∧
      (centerIdeal K n c).map φ = Z.stalkIdeal x ∧
      (centerIdeal K n c).map φ ≠ ⊤ ∧
      Z.comap (X.fromSpecStalk x) = specIdealSheaf ((centerIdeal K n c).map φ) := by
  obtain ⟨z, hz⟩ := Z.exists_subschemeι_eq hx
  obtain ⟨y, hy⟩ := exists_adaptedChart_mem f n c Z hcn z
  obtain ⟨φ, hφ, hI⟩ := etaleAdapted_exists_flat_stalk_coordinates
    (adaptedChart f n c Z hcn y) x (hz ▸ hy)
  have heq : (centerIdeal K n c).map φ = Z.stalkIdeal x := by
    apply specIdealSheaf_injective (X.presheaf.stalk x)
    rw [← hI, comap_fromSpecStalk_eq_specIdealSheaf]
    rfl
  refine ⟨φ, hφ, heq, ?_, hI⟩
  rw [heq]
  have hm := (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx
  exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm

end MixedFujita
