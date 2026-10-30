/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PointClosureCenterMap
public import MixedFujita.CartierSectionSNCPerturbation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! 他成分を避け滑らかな中心閉点へ写る実素因子閉点。 See reports/check-265-lc-center-positive-numerical-descent.json for the verified scope. Actual lc-center geometry supplies an internal critical proper SNC model, prime-to-center map and good smooth closed center point. Intrinsic stalk orders transfer actual natural restriction concentration to the critical component. Positive RESTRICTED numerical dimension yields all-high original nonzero sections, original ambient nonLC and all exterior LC. For a normal source with effective boundary and minimal center, one strict lower-dimensional minimal integral center is constructed preserving all large ORIGINAL L-adjoint ampleness. Restricted numerical-zero branches, full descent iteration, initial original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable


/-- On an ACTUAL prime closure of a proper model, choose a closed point away
from all other listed primes, smooth on that closure, whose actual center
image is a smooth closed point of the actual reduced center. The factor map
and generic-point control are internal. No center normality or SNC is needed. -/
theorem exists_prime_closure_good_closed_point_over_smooth_center
    {K : Type u} [Field K] [PerfectField K] {T X : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsProper ρ] {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1) (i₀ : Fin r) :
    ∃ ψ : pointClosureScheme (ξ i₀) ⟶ pointClosureScheme (ρ (ξ i₀)),
      ψ ≫ pointClosureι (ρ (ξ i₀)) = pointClosureι (ξ i₀) ≫ ρ ∧
      ∃ z : pointClosureScheme (ξ i₀), IsClosed ({z} : Set (pointClosureScheme (ξ i₀))) ∧
        IsClosed ({pointClosureι (ξ i₀) z} : Set T) ∧
        IsClosed ({ψ z} : Set (pointClosureScheme (ρ (ξ i₀)))) ∧
        ψ z ∈ (pointClosureScheme (ρ (ξ i₀)) ↘ Spec (CommRingCat.of K)).smoothLocus ∧
        z ∈ (pointClosureScheme (ξ i₀) ↘ Spec (CommRingCat.of K)).smoothLocus ∧
        ∀ i, i ≠ i₀ → pointClosureι (ξ i₀) z ∉ closure ({ξ i} : Set T) := by
  classical
  obtain ⟨ψ, hfac, hgen⟩ := exists_point_closure_map_preserving_genericPoint ρ (ξ i₀)
  have : IsProper (ψ ≫ pointClosureι (ρ (ξ i₀))) := by rw [hfac]; infer_instance
  have : IsProper ψ := IsProper.of_comp ψ (pointClosureι (ρ (ξ i₀)))
  let C : Set T := ⋃ i ∈ Finset.univ.erase i₀, closure ({ξ i} : Set T)
  have hC : IsClosed C := isClosed_biUnion_finset fun i _ => isClosed_closure
  have hnot : pointClosureι (ξ i₀) (genericPoint (pointClosureScheme (ξ i₀))) ∉ C := by
    rw [pointClosureι_genericPoint]
    intro h
    simp only [C, Set.mem_iUnion] at h
    obtain ⟨i, hi, hmem⟩ := h
    have he := (scheme_codimensionOne_mem_closure_iff_eq (ξ i₀) (ξ i) (hξ i₀) (hξ i)).mp hmem
    exact (Finset.mem_erase.mp hi).1 (hinj he).symm
  let A := (pointClosureScheme (ξ i₀) ↘ Spec (CommRingCat.of K)).smoothLocus
  let B := (pointClosureScheme (ρ (ξ i₀)) ↘ Spec (CommRingCat.of K)).smoothLocus
  let G : Set (pointClosureScheme (ξ i₀)) := ((A : Set _) ∩ ψ ⁻¹' (B : Set _)) ∩
    pointClosureι (ξ i₀) ⁻¹' Cᶜ
  have hG : IsOpen G := (A.isOpen.inter (B.isOpen.preimage ψ.continuous)).inter
    (hC.isOpen_compl.preimage (pointClosureι (ξ i₀)).continuous)
  have hGgen : genericPoint (pointClosureScheme (ξ i₀)) ∈ G := by
    refine ⟨⟨?_, ?_⟩, hnot⟩
    · exact (pointClosureScheme (ξ i₀) ↘ Spec (CommRingCat.of K)).genericPoint_mem_smoothLocus_of_perfectField
    · change ψ _ ∈ B
      rw [hgen]
      exact (pointClosureScheme (ρ (ξ i₀)) ↘ Spec (CommRingCat.of K)).genericPoint_mem_smoothLocus_of_perfectField
  have : JacobsonSpace (pointClosureScheme (ξ i₀)) :=
    LocallyOfFiniteType.jacobsonSpace (pointClosureScheme (ξ i₀) ↘ Spec (CommRingCat.of K))
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints ⟨_, hGgen⟩ hG.isLocallyClosed
  have hzcl : IsClosed ({z} : Set (pointClosureScheme (ξ i₀))) := mem_closedPoints_iff.mp hzc
  refine ⟨ψ, hfac, z, hzcl, ?_, ?_, hz.1.2, hz.1.1, ?_⟩
  · simpa only [Set.image_singleton] using (pointClosureι (ξ i₀)).isClosedEmbedding.isClosedMap _ hzcl
  · simpa only [Set.image_singleton] using ψ.isClosedMap _ hzcl
  · intro i hi hmem
    apply hz.2
    simp only [C, Set.mem_iUnion]
    exact ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hmem⟩

end MixedFujita
