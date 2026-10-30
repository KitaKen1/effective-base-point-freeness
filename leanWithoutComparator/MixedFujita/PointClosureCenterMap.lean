/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PointClosureSubscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! 素因子被約閉包から実被約中心への射と一般点。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable


/-- The ACTUAL reduced point closure maps to ANY actual reduced closed center
containing the image of its generic point. Mathlib's map_vanishingIdeal gives
the scheme factorization directly, with no extra reduced-map kernel proof. -/
theorem exists_point_closure_map_to_reduced_closed_center
    {T X : Scheme.{u}} (ρ : T ⟶ X) (ξ : T) (Z : Closeds X) (hξ : ρ ξ ∈ Z) :
    let J := Scheme.IdealSheafData.vanishingIdeal (⟨closure ({ξ} : Set T), isClosed_closure⟩ : Closeds T)
    let I := Scheme.IdealSheafData.vanishingIdeal Z
    ∃ ψ : J.subscheme ⟶ I.subscheme, ψ ≫ I.subschemeι = J.subschemeι ≫ ρ := by
  dsimp only
  let C : Closeds T := ⟨closure ({ξ} : Set T), isClosed_closure⟩
  let J := Scheme.IdealSheafData.vanishingIdeal C
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have himage : ρ '' (C : Set T) ⊆ (Z : Set X) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ((specializes_iff_mem_closure.mpr ht).map ρ.continuous).mem_closed Z.isClosed hξ
  have hle : I ≤ J.map ρ := by
    change Scheme.IdealSheafData.vanishingIdeal Z ≤ (Scheme.IdealSheafData.vanishingIdeal C).map ρ
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (closure_minimal himage Z.isClosed)
  exact ⟨J.subschemeMap I ρ hle, J.subschemeMap_subschemeι I ρ hle⟩


/-- The actual point-closure map also maps the generic point to the generic
point. This supplies a nonempty inverse image of the smooth center locus. -/
theorem exists_point_closure_map_preserving_genericPoint
    {T X : Scheme.{u}} (ρ : T ⟶ X) (ξ : T) :
    ∃ ψ : pointClosureScheme ξ ⟶ pointClosureScheme (ρ ξ),
      ψ ≫ pointClosureι (ρ ξ) = pointClosureι ξ ≫ ρ ∧
      ψ (genericPoint (pointClosureScheme ξ)) = genericPoint (pointClosureScheme (ρ ξ)) := by
  obtain ⟨ψ, hψ⟩ := exists_point_closure_map_to_reduced_closed_center ρ ξ
    ⟨closure ({ρ ξ} : Set X), isClosed_closure⟩ (subset_closure rfl)
  refine ⟨ψ, hψ, ?_⟩
  apply (pointClosureι (ρ ξ)).isEmbedding.injective
  calc
    pointClosureι (ρ ξ) (ψ (genericPoint (pointClosureScheme ξ))) =
        ρ (pointClosureι ξ (genericPoint (pointClosureScheme ξ))) :=
      congrArg (fun h : pointClosureScheme ξ ⟶ X => h (genericPoint (pointClosureScheme ξ))) hψ
    _ = ρ ξ := congrArg ρ (pointClosureι_genericPoint ξ)
    _ = pointClosureι (ρ ξ) (genericPoint (pointClosureScheme (ρ ξ))) :=
      (pointClosureι_genericPoint (ρ ξ)).symm

end MixedFujita
