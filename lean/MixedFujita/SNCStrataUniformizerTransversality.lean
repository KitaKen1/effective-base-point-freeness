/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothClosedStratumTransversality
public import MixedFujita.SNCStrataGenericSmoothness

/-!
On the internally constructed common smooth-strata base open, every base-prime
uniformizer is transverse to every actual closed SNC stratum. The transverse
condition is the intrinsic nonmembership in the ambient maximal-ideal square
plus the actual stratum ideal. It is a proved conclusion, not an input certificate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Every base-prime uniformizer is transverse to every actual closed SNC stratum over this open. -/
def SNCStrataUniformizerTransverseOn {T Y : Scheme.{u}} (g : T ⟶ Y)
    (E : Scheme.DivisorFamily T) (V : Y.Opens) : Prop :=
  ∀ s : Finset E.ι,
    let J := sncStratumIdeal E s
    ∀ w : J.subscheme, g (J.subschemeι w) ∈ V → Order.coheight (g (J.subschemeι w)) = 1 →
      ∀ a : Y.presheaf.stalk (g (J.subschemeι w)), Irreducible a →
        (g.stalkMap (J.subschemeι w)).hom a ∉
          maximalIdeal (T.presheaf.stalk (J.subschemeι w)) ^ 2 ⊔ J.stalkIdeal (J.subschemeι w)

/-- Smoothness of an actual base restriction implies membership in the original smooth locus. -/
theorem mem_smoothLocus_of_smooth_morphismRestrict
    {T Y : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFinitePresentation g]
    (V : Y.Opens) [Smooth (g ∣_ V)] (t : T) (ht : g t ∈ V) : t ∈ g.smoothLocus := by
  have h : (⟨t, ht⟩ : (g ⁻¹ᵁ V).toScheme) ∈ (g ∣_ V).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rw [Scheme.Hom.mem_smoothLocus] at h ⊢
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap g V ⟨t, ht⟩)).mp h

/-- Smooth restrictions of all closed SNC strata prove the actual uniformizer transversality. -/
theorem sncStrataUniformizerTransverseOn_of_smooth_restrictions
    {K : Type u} [Field K] [PerfectField K] {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))] [Smooth (T ↘ Spec (CommRingCat.of K))]
    [IsLocallyNoetherian T] [IsIntegral Y] [IsLocallyNoetherian Y]
    [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [IsProper g] (E : Scheme.DivisorFamily T) (hE : E.IsSnc)
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (V : Y.Opens)
    (hV : ∀ s : Finset E.ι, Smooth (((sncStratumIdeal E s).subschemeι ≫ g) ∣_ V)) :
    SNCStrataUniformizerTransverseOn g E V := by
  intro s
  dsimp only
  intro w hw hcoh a ha
  let J := sncStratumIdeal E s
  let q := J.subschemeι ≫ g
  letI : Smooth (q ∣_ V) := hV s
  have hsm := mem_smoothLocus_of_smooth_morphismRestrict q V w hw
  letI := hnormY (q w)
  exact smooth_closed_stratum_uniformizer_transverse (K := K) g J w hsm hcoh
    ((sncStratum_isRegular K E hE s).isRegularAt w) a ha

/-- Construct one nonempty base open on which all actual closed SNC strata are uniformly transverse. -/
theorem proper_snc_strata_exists_uniformizer_transverse_base_open
    {K : Type u} [Field K] [CharZero K] {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))] [Smooth (T ↘ Spec (CommRingCat.of K))]
    [IsLocallyNoetherian T] [IsIntegral Y] [IsLocallyNoetherian Y]
    [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [IsProper g] (E : Scheme.DivisorFamily T) (hE : E.IsSnc)
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧
      (∀ s : Finset E.ι, Smooth (((sncStratumIdeal E s).subschemeι ≫ g) ∣_ V)) ∧
      SNCStrataUniformizerTransverseOn g E V := by
  obtain ⟨V, hηV, hV⟩ := proper_snc_strata_exists_common_smooth_base_open K g E hE
  exact ⟨V, hηV, hV,
    sncStrataUniformizerTransverseOn_of_smooth_restrictions (K := K) g E hE hnormY V hV⟩

end MixedFujita
