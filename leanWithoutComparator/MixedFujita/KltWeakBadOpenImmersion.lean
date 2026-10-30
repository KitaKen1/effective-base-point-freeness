/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltFixedIdealLemmaThree
public import MixedFujita.WeakModelThresholdBad
public import MixedFujita.DominantOpenBaseRestriction

/-!
Weak badness along open immersions (step 15, the klt restriction theorem).

Let j : Z → X be an open immersion and z a point of Z. If the pair (c, f, d, D) on X has threshold
at most 1/M at j(z) for a family g in the weak model form, then so has the pulled back pair
(c_Z, j*ω, d, j*D) on Z at z for the pulled back family
(`modelThresholdWeakBadAt_openImmersion_pullback`): the centre j(z) of a test prime e of
σ : U → X lies in the open range of j, hence so does σ(e), and the part σ⁻¹(j(Z)) of U, lifted
through j, is a test model of Z with the same discrepancy and the same orders along e.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))

set_option maxHeartbeats 1600000 in
/-- **Weak badness along an open immersion**: weak badness of a pair on X at j(z) gives weak badness
of the pulled back pair, with the pulled back form j*ω in the chart c_Z, at z for the pulled back
family. -/
theorem modelThresholdWeakBadAt_openImmersion_pullback (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (cZ : EtaleChart K Z n) (z : Z)
    {J : Type*} (gX : J → X.functionField) (gZ : J → Z.functionField)
    (hg : ∀ i, (dominantFunctionFieldMap j).hom (gX i) = gZ i) (M : ℕ)
    (h : ModelThresholdWeakBadAt c f d D (j z) gX M) :
    ModelThresholdWeakBadAt cZ (crepantPullbackFormUnit j hj c f cZ) d (cartierPullback j D) z
      gZ M := by
  classical
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hze, hineq⟩ := h
  have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  -- the part of the test model over the open range of j
  let V : X.Opens := j.opensRange
  have heV : σ (e : U) ∈ V :=
    (specializes_iff_mem_closure.mpr hze).mem_open V.isOpen ⟨z, rfl⟩
  let U' : U.Opens := σ ⁻¹ᵁ V
  have : Nonempty U' := ⟨⟨(e : U), heV⟩⟩
  let : U'.toScheme.Over (Spec (CommRingCat.of K)) := ⟨U'.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  have : U'.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant U'.ι := ⟨U'.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : IsIntegral U'.toScheme := isIntegral_of_isOpenImmersion U'.ι
  have : SmoothOfRelativeDimension n (U'.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := U'.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (U'.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have hrange : Set.range (U'.ι ≫ σ) ⊆ Set.range j := by
    rintro _ ⟨u, rfl⟩
    exact u.2
  let σ' : U'.toScheme ⟶ Z := IsOpenImmersion.lift j (U'.ι ≫ σ) hrange
  have hsq : σ' ≫ j = U'.ι ≫ σ := IsOpenImmersion.lift_fac j (U'.ι ≫ σ) hrange
  -- σ' is a dominant birational morphism over K
  have hgen : σ' (genericPoint U'.toScheme) = genericPoint Z := by
    apply j.isOpenEmbedding.injective
    have h1 := congrArg (fun g : U'.toScheme ⟶ X => g (genericPoint U'.toScheme)) hsq
    simp only [Scheme.Hom.comp_apply] at h1
    rw [h1, dominant_map_genericPoint U'.ι, dominant_map_genericPoint σ,
      dominant_map_genericPoint j]
  haveI hσ'd : IsDominant σ' := by
    constructor
    rw [DenseRange, dense_iff_closure_eq]
    apply Set.eq_univ_of_univ_subset
    have hcl : closure ({genericPoint Z} : Set Z) = Set.univ := (genericPoint_spec Z).def
    rw [← hcl]
    exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint U'.toScheme, hgen⟩)
  have hσ'o : σ'.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    have h1 : σ' ≫ j ≫ (X ↘ Spec (CommRingCat.of K)) = σ' ≫ (Z ↘ Spec (CommRingCat.of K)) := by
      rw [HomIsOver.comp_over]
    rw [← h1, ← Category.assoc, hsq, Category.assoc, HomIsOver.comp_over, HomIsOver.comp_over]
  have hU'ι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) U'.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion U'.ι
  have hσ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ') := by
    have h2 := dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι
    rw [← dominantFunctionFieldAlgHom_congr_hom hsq, dominantFunctionFieldAlgHom_comp,
      AlgHom.coe_comp] at h2
    exact (Function.Bijective.of_comp_iff _ hj).mp h2
  -- the test prime on the part over the range of j
  have hbij : Function.Bijective (U'.ι.stalkMap ⟨(e : U), heV⟩) :=
    ConcreteCategory.bijective_of_isIso _
  let e' : CodimensionOnePoint U'.toScheme :=
    ⟨⟨(e : U), heV⟩, (coheight_eq_of_stalkMap_bijective U'.ι ⟨(e : U), heV⟩ hbij).trans e.property⟩
  obtain ⟨cU'⟩ : Nonempty (EtaleChart K U'.toScheme n) := by
    obtain ⟨c, -⟩ := Opens.mem_iSup.mp
      ((etaleCharts_cover (K := K) (X := U'.toScheme) (n := n)).symm ▸
        Opens.mem_top (e' : U'.toScheme))
    exact ⟨c⟩
  have hσe : j (σ' (e' : U'.toScheme)) = σ (e : U) := by
    have h1 := congrArg (fun g : U'.toScheme ⟶ X => g (e' : U'.toScheme)) hsq
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1
  refine ⟨U'.toScheme, inferInstance, inferInstance, inferInstance, inferInstance, σ', hσ'd, hσ'o,
    hσ', cU', e', ?_, fun i hi => ?_⟩
  · apply (mem_closure_singleton_open_immersion_iff j (σ' (e' : U'.toScheme)) z).mp
    rw [hσe]
    exact hze
  · -- the discrepancies agree
    have hlog : cartierCoefficient (logDiscrepancyDivisor n σ' hσ' cZ
        (crepantPullbackFormUnit j hj c f cZ) d (cartierPullback j D) cU' etaleCharts_cover)
        (e' : U'.toScheme) = cartierCoefficient (logDiscrepancyDivisor n σ hσ c f d D cU
          etaleCharts_cover) (e : U) := by
      rw [← logDiscrepancyDivisor_comp j σ' hj hσ' c f d D cZ cU' etaleCharts_cover,
        logDiscrepancyDivisor_congr_hom hsq _
          (dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι)]
      exact logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ U'.ι hσ hU'ι c f d D
        cU cU' e' e.property hbij
    -- the orders agree
    have hgX : gX i ≠ 0 := by
      intro h0
      apply hi
      rw [← hg i, h0, map_zero]
    have hord : U'.toScheme.ord ((dominantFunctionFieldMap σ').hom (gZ i)) (e' : U'.toScheme) =
        U.ord ((dominantFunctionFieldMap σ).hom (gX i)) (e : U) := by
      have : Smooth (U'.toScheme ↘ Spec (CommRingCat.of K)) :=
        SmoothOfRelativeDimension.smooth n _
      have := smoothOverField_codimensionOne_stalk_DVR (K := K)
        (⟨U'.ι (e' : U'.toScheme), e.property⟩ : CodimensionOnePoint U)
      have := smoothOverField_codimensionOne_stalk_DVR (K := K) e'
      have h1 : (dominantFunctionFieldMap σ').hom (gZ i) =
          (dominantFunctionFieldMap U'.ι).hom ((dominantFunctionFieldMap σ).hom (gX i)) := by
        rw [← hg i]
        have e1 : ∀ x, dominantFunctionFieldAlgHom (K := K) (σ' ≫ j) x =
            dominantFunctionFieldAlgHom (K := K) σ' (dominantFunctionFieldAlgHom (K := K) j x) :=
          fun x => by rw [dominantFunctionFieldAlgHom_comp]; rfl
        have e2 : ∀ x, dominantFunctionFieldAlgHom (K := K) (U'.ι ≫ σ) x =
            dominantFunctionFieldAlgHom (K := K) U'.ι (dominantFunctionFieldAlgHom (K := K) σ x) :=
          fun x => by rw [dominantFunctionFieldAlgHom_comp]; rfl
        change dominantFunctionFieldAlgHom (K := K) σ' (dominantFunctionFieldAlgHom (K := K) j (gX i)) =
          dominantFunctionFieldAlgHom (K := K) U'.ι (dominantFunctionFieldAlgHom (K := K) σ (gX i))
        rw [← e1, ← e2, dominantFunctionFieldAlgHom_congr_hom hsq]
      let u : U.functionFieldˣ := Units.mk0 ((dominantFunctionFieldMap σ).hom (gX i))
        ((map_ne_zero _).mpr hgX)
      have h2 := cartierCoefficient_pullback_of_stalkMap_bijective U'.ι e' e.property hbij
        (principalCartierDivisor U u)
      rw [cartierPullback_principal, cartierCoefficient_principal, cartierCoefficient_principal]
        at h2
      rw [h1]
      exact h2
    rw [hlog, hord]
    exact hineq i hgX

end MixedFujita
