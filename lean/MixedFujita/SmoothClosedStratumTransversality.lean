/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothBasePrimeParameters
public import Hironaka.Scheme.Smooth.SubschemeStalk

/-!
A uniformizer which is a parameter on an actual closed stratum is transverse
to the stratum in the ambient stalk: it is not in the sum of the square of the
ambient maximal ideal and the actual stratum ideal. Use the actual closed
immersion stalk map and its actual kernel, without a quotient comparison input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A nonzero cotangent class after a local quotient excludes the ambient square plus kernel. -/
theorem localMap_notMem_sq_implies_notMem_sq_sup_kernel
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] (I : Ideal R) (hI : RingHom.ker φ = I)
    (a : R) (ha : φ a ∉ maximalIdeal S ^ 2) : a ∉ maximalIdeal R ^ 2 ⊔ I := by
  intro h
  obtain ⟨q, hq, w, hw, heq⟩ := Submodule.mem_sup.mp h
  have hle : Ideal.map φ (maximalIdeal R ^ 2) ≤ maximalIdeal S ^ 2 := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (map_maximalIdeal_le φ) 2
  have hqmap : φ q ∈ maximalIdeal S ^ 2 := hle (Ideal.mem_map_of_mem φ hq)
  have hwzero : φ w = 0 := RingHom.mem_ker.mp (hI.symm ▸ hw)
  apply ha
  rw [← heq, map_add, hwzero, add_zero]
  exact hqmap

/-- Smoothness of an actual closed stratum makes the base uniformizer transverse in the ambient stalk. -/
theorem smooth_closed_stratum_uniformizer_transverse
    {K : Type u} [Field K] [PerfectField K] {T Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : T ⟶ Y) (J : T.IdealSheafData) [LocallyOfFinitePresentation (J.subschemeι ≫ g)]
    (w : J.subscheme) (hsm : w ∈ (J.subschemeι ≫ g).smoothLocus)
    (hcoh : Order.coheight ((J.subschemeι ≫ g) w) = 1)
    [IsIntegrallyClosed (Y.presheaf.stalk ((J.subschemeι ≫ g) w))]
    (hreg : J.subscheme.IsRegularAt w)
    (a : Y.presheaf.stalk ((J.subschemeι ≫ g) w)) (ha : Irreducible a) :
    (g.stalkMap (J.subschemeι w)).hom a ∉ maximalIdeal (T.presheaf.stalk (J.subschemeι w)) ^ 2 ⊔
      J.stalkIdeal (J.subschemeι w) := by
  have h := (smooth_base_prime_stalk_uniformizer_notMem_sq (K := K)
    (J.subschemeι ≫ g) w hsm hcoh hreg a ha).2
  apply localMap_notMem_sq_implies_notMem_sq_sup_kernel (J.subschemeι.stalkMap w).hom
    (J.stalkIdeal (J.subschemeι w)) (J.ker_stalkMap_subschemeι w) ((g.stalkMap (J.subschemeι w)).hom a)
  have heq : (J.subschemeι.stalkMap w).hom ((g.stalkMap (J.subschemeι w)).hom a) =
      ((J.subschemeι ≫ g).stalkMap w).hom a := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [heq]
  exact h

end MixedFujita
