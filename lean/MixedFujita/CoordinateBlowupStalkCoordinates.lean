/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialMorphismStalkCoordinates
public import MixedFujita.EtaleCoordinateBlowupCharts

/-! Matched formally etale coordinates at actual stalks of a coordinate-center
blow-up. The chart equations and nonunit exceptional coordinate are constructed
on the entire inverse image of an adapted neighborhood. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme.Hom
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n r : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of K))] {f : X ⟶ Spec (.of K)} {Z : X.IdealSheafData} {x : X}
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

omit [X.Over (Spec (.of K))] in
theorem etaleCoordinateBlowupChart_exceptionalIdeal_affine
    (E : EtaleCoordinatesAdapted f n r Z x) (k : Fin n) (hk : k.val < r)
    (V : (etaleCoordinateBlowupChart E k hk).affineOpens) :
    (((Z.comap E.U.1.ι).comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))).comap
      (pullback.fst (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk))).ideal V =
      Ideal.span {(sectionsHom
        (pullback.snd (etaleCoordinateBlowupModelMap E)
          (CoordinateSubspace.modelChart K n r k hk)) V.1 (MvPolynomial.X k))} := by
  rw [etaleCoordinateBlowupChart_exceptionalIdeal]
  change ((specIdealSheaf (Ideal.span {(MvPolynomial.X k : MvPolynomial (Fin n) K)})).comap
    (pullback.snd (etaleCoordinateBlowupModelMap E)
      (CoordinateSubspace.modelChart K n r k hk))).ideal V = _
  erw [ideal_comap_specIdealSheaf]
  rw [Ideal.map_span, Set.image_singleton]

noncomputable def etaleCoordinateBlowupChartToGlobal (E : EtaleCoordinatesAdapted f n r Z x)
    (k : Fin n) (hk : k.val < r) : etaleCoordinateBlowupChart E k hk ⟶ Z.blowUp :=
  pullback.fst (etaleCoordinateBlowupModelMap E)
    (CoordinateSubspace.modelChart K n r k hk) ≫ blowUpMap E.U.1.ι Z

instance etaleCoordinateBlowupChartToGlobal_openImmersion (E : EtaleCoordinatesAdapted f n r Z x)
    (k : Fin n) (hk : k.val < r) : IsOpenImmersion (etaleCoordinateBlowupChartToGlobal E k hk) := by
  have : IsOpenImmersion (blowUpMap E.U.1.ι Z) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_blowUpMap E.U.1.ι Z).flip inferInstance
  unfold etaleCoordinateBlowupChartToGlobal
  infer_instance

omit [X.Over (Spec (.of K))] in
theorem etaleCoordinateBlowupChartToGlobal_covers_fibre (E : EtaleCoordinatesAdapted f n r Z x)
    (q : Z.blowUp) (hq : Z.blowUpπ q ∈ E.U.1) :
    ∃ (k : Fin n) (hk : k.val < r) (p : etaleCoordinateBlowupChart E k hk), etaleCoordinateBlowupChartToGlobal E k hk p = q := by
  obtain ⟨qU, hqU, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_blowUpMap E.U.1.ι Z) q (⟨Z.blowUpπ q, hq⟩ : E.U.1) rfl
  obtain ⟨k, hk, p, hp⟩ := etaleCoordinateBlowupChart_exists_preimage E qU
  exact ⟨k, hk, p, (congrArg (blowUpMap E.U.1.ι Z) hp).trans hqU⟩

theorem etaleCoordinateBlowupChartToGlobal_comp_base
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n r Z x) (k : Fin n) (hk : k.val < r) :
    etaleCoordinateBlowupChartToGlobal E k hk ≫ Z.blowUpπ ≫ (X ↘ Spec (.of K)) =
      pullback.snd (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K))) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))
  have hscalar : Spec.map (CommRingCat.ofHom (affineBlowUpAlgebra.chartSubst K (CoordinateSubspace.center n r) k).toRingHom) ≫
      c = c := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (affineBlowUpAlgebra.chartSubst K (CoordinateSubspace.center n r) k).comp_algebraMap
  have h := congrArg (fun g => g ≫ c) (etaleCoordinateBlowupChart_projection E k hk)
  simp only [Category.assoc, hscalar] at h
  dsimp only [c] at h
  rw [toAffineSpace_comp_structure] at h
  rw [etaleCoordinateBlowupChartToGlobal, Category.assoc, blowUpMap_π_assoc]
  exact h

theorem etaleCoordinateBlowupChartToGlobal_comp_projection
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n r Z x) (k : Fin n) (hk : k.val < r) :
    etaleCoordinateBlowupChartToGlobal E k hk ≫ Z.blowUpπ =
      pullback.fst (etaleCoordinateBlowupModelMap E)
        (CoordinateSubspace.modelChart K n r k hk) ≫
        (Z.comap E.U.1.ι).blowUpπ ≫ E.U.1.ι := by
  rw [etaleCoordinateBlowupChartToGlobal, Category.assoc, blowUpMap_π]

set_option maxHeartbeats 800000 in
theorem etaleCoordinateBlowup_matched_stalk_coordinates
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n r Z x)
    (q : Z.blowUp) (hq : Z.blowUpπ q ∈ E.U.1) (hqZ : Z.blowUpπ q ∈ Z.support) :
    let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ (k : Fin n) (_hk : k.val < r) (τ : MvPolynomial (Fin n) K →ₐ[K] Z.blowUp.presheaf.stalk q),
      τ.toRingHom.FormallyEtale ∧ ¬ IsUnit (τ (MvPolynomial.X k)) ∧
      ∀ i, Z.blowUpπ.stalkMap q
        (X.presheaf.germ E.U.1 (Z.blowUpπ q) hq (E.v i)) =
        if i = k then τ (MvPolynomial.X k) else if i.val < r then τ (MvPolynomial.X i) * τ (MvPolynomial.X k)
        else τ (MvPolynomial.X i) := by
  let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
  obtain ⟨k, hk, p, rfl⟩ := etaleCoordinateBlowupChartToGlobal_covers_fibre E q hq
  let Y := etaleCoordinateBlowupChart E k hk
  let σ := pullback.snd (etaleCoordinateBlowupModelMap E)
    (CoordinateSubspace.modelChart K n r k hk)
  let : Y.Over (Spec (.of K)) :=
    ⟨σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))⟩
  let ρ := etaleCoordinateBlowupChartToGlobal E k hk
  have : ρ.IsOver (Spec (.of K)) := ⟨etaleCoordinateBlowupChartToGlobal_comp_base E k hk⟩
  let a := pullback.fst (etaleCoordinateBlowupModelMap E)
    (CoordinateSubspace.modelChart K n r k hk) ≫ (Z.comap E.U.1.ι).blowUpπ
  have hμ : a ≫ E.U.1.ι = ρ ≫ Z.blowUpπ :=
    (etaleCoordinateBlowupChartToGlobal_comp_projection E k hk).symm
  obtain ⟨V, hp⟩ := Scheme.IdealSheafData.exists_affineOpens_mem p
  let τY := polynomialStalkAlgHom σ rfl V p hp
  let e := AlgEquiv.ofBijective (schemeStalkMapAlgHom (K := K) ρ p)
    (ConcreteCategory.bijective_of_isIso (ρ.stalkMap p))
  let τ := e.symm.toAlgHom.comp τY
  have hτ : τ.toRingHom.FormallyEtale := RingHom.FormallyEtale.comp
    (polynomialStalkAlgHom_formallyEtale σ rfl V p hp)
    (ringHom_formallyEtale_of_etale e.symm.toRingEquiv.toRingHom
      (RingHom.Etale.of_bijective e.symm.bijective))
  have hcoords (i : Fin n) : ρ.stalkMap p
      (Z.blowUpπ.stalkMap (ρ p) (X.presheaf.germ E.U.1 (Z.blowUpπ (ρ p))
        hq (E.v i))) = τY (affineBlowUpAlgebra.chartSubst K (CoordinateSubspace.center n r) k (MvPolynomial.X i)) := by
    have h := germ_sectionsHom_toAffineSpace (X ↘ Spec (.of K)) E.U.1 E.v a V.1 p hp i
    have hg : (a ≫ E.U.1.ι).stalkMap p
        (X.presheaf.germ E.U.1 ((a ≫ E.U.1.ι) p) (a p).2 (E.v i)) =
        ρ.stalkMap p (Z.blowUpπ.stalkMap (ρ p)
          (X.presheaf.germ E.U.1 (Z.blowUpπ (ρ p)) hq (E.v i))) := by
      exact (stalkMap_germ_congr hμ E.U.1 p (a p).2 hq (E.v i)).trans
        (congrArg (fun g => g (X.presheaf.germ E.U.1 (Z.blowUpπ (ρ p))
          hq (E.v i))) (Scheme.Hom.stalkMap_comp ρ Z.blowUpπ p))
    rw [hg] at h
    rw [show a ≫ toAffineSpace (X ↘ Spec (.of K)) E.U.1 E.v =
      σ ≫ Spec.map (CommRingCat.ofHom (affineBlowUpAlgebra.chartSubst K (CoordinateSubspace.center n r) k).toRingHom) from
        etaleCoordinateBlowupChart_projection E k hk, sectionsHom_comp_specMap] at h
    exact h.symm
  let J := ((Z.comap E.U.1.ι).comap (Z.comap E.U.1.ι).blowUpπ).comap
    (pullback.fst (etaleCoordinateBlowupModelMap E) (CoordinateSubspace.modelChart K n r k hk))
  have hJ : J = Z.comap (ρ ≫ Z.blowUpπ) := by
    dsimp [J]
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← hμ]
  have hpJ : p ∈ J.support := by
    rw [hJ, Scheme.IdealSheafData.support_comap]
    change Z.blowUpπ (ρ p) ∈ Z.support
    exact hqZ
  have hnonunitY : ¬ IsUnit (τY (MvPolynomial.X k)) := by
    have hzero := (J.mem_support_iff_of_mem (U := V) hp).mp hpJ
    have hmem : sectionsHom σ V.1 (MvPolynomial.X k) ∈ J.ideal V := by
      rw [show J.ideal V = _ from etaleCoordinateBlowupChart_exceptionalIdeal_affine E k hk V]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hn := (Y.mem_zeroLocus_iff _ p).mp hzero _ hmem
    exact fun hu => hn ((Y.mem_basicOpen _ p hp).mpr hu)
  have heτ (g : MvPolynomial (Fin n) K) : e (τ g) = τY g := by
    change e (e.symm (τY g)) = τY g
    exact e.apply_symm_apply _
  refine ⟨k, hk, τ, hτ, ?_, ?_⟩
  · intro hu
    apply hnonunitY
    have he := hu.map e.toRingHom
    change IsUnit (e (τ (MvPolynomial.X k))) at he
    rwa [heτ] at he
  · intro i
    apply e.injective
    by_cases hi : i = k
    · rw [ite_eq_left hi, heτ]
      change ρ.stalkMap p (Z.blowUpπ.stalkMap (ρ p) _) = _
      simpa only [hi, affineBlowUpAlgebra.chartSubst_X_self] using hcoords i
    · by_cases hir : i.val < r
      · rw [ite_eq_right hi, ite_eq_left hir, map_mul, heτ, heτ]
        change ρ.stalkMap p (Z.blowUpπ.stalkMap (ρ p) _) = _
        simpa only [CoordinateSubspace.chartSubst_X, ne_eq, hir, hi, not_false_eq_true,
          true_and, ite_true, map_mul] using hcoords i
      · rw [ite_eq_right hi, ite_eq_right hir, heτ]
        change ρ.stalkMap p (Z.blowUpπ.stalkMap (ρ p) _) = _
        simpa only [CoordinateSubspace.chartSubst_X, hir, false_and, ite_false] using hcoords i

end MixedFujita
