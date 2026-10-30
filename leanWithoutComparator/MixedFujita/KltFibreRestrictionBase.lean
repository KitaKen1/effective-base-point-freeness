/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltGenericRestriction

/-!
Restriction to the fibres of products when the base has no coordinates (step 15, the base case
of the induction on the number of coordinates).

A domain B of finite type over an algebraically closed field K with formally étale coordinates
φ : K[∅] = K → B is K itself (`algebraMap_bijective_of_formallyEtale_fin_zero`: a localization of
B at a maximal ideal is local, unramified and essentially of finite type over K, hence K). Then
the second projection of P = Spec B ×_K Y is an isomorphism, the fibre over the K-point w of B is
its inverse, and the product chart has the coordinates of c_Y, so the product pair is the
pullback of the pair of Y (`chartRelativeJacobianDet_fibreProduct_fin_zero`). A weakly bad point
of the product is therefore a weakly bad point of Y, hence bad for a klt pair
(`modelThresholdBadAt_fibre_of_fin_zero`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra functionFieldBaseAlgebra specAlgebraOver structureSectionsAlgebra
  specFibreProductOverAlgebra specFibreProductOverField specFibreProduct_isScalarTower
  specFibreProductSnd_isDominant specFibreProductSnd_isOver

section Base

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **A domain of finite type with formally étale coordinates in no variables over an
algebraically closed field is the field itself.** -/
theorem algebraMap_bijective_of_formallyEtale_fin_zero {B : Type u} [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] (φ : MvPolynomial (Fin 0) K →ₐ[K] B)
    (hφ : φ.toRingHom.FormallyEtale) : Function.Bijective (algebraMap K B) := by
  have hK : (algebraMap K (MvPolynomial (Fin 0) K)).FormallyEtale := by
    have hb : Function.Bijective (algebraMap K (MvPolynomial (Fin 0) K)) :=
      (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).symm.bijective
    exact ringHom_formallyEtale_of_etale _ (RingHom.Etale.of_bijective hb)
  have h1 : algebraMap K B = φ.toRingHom.comp (algebraMap K (MvPolynomial (Fin 0) K)) := by
    ext k
    simp
  have : Algebra.FormallyEtale K B := by
    rw [← RingHom.formallyEtale_algebraMap, h1]
    exact RingHom.FormallyEtale.comp hK hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let Bm := Localization.AtPrime m
  have : Algebra.FormallyEtale B Bm := Algebra.FormallyEtale.of_isLocalization m.primeCompl
  have : Algebra.FormallyUnramified K Bm := Algebra.FormallyUnramified.comp K B Bm
  have : Algebra.EssFiniteType B Bm := Algebra.EssFiniteType.of_isLocalization Bm m.primeCompl
  have : Algebra.EssFiniteType K Bm := Algebra.EssFiniteType.comp K B Bm
  have hbij := Algebra.FormallyUnramified.bijective_of_isAlgClosed_of_isLocalRing K Bm
  have hinj : Function.Injective (algebraMap B Bm) :=
    IsLocalization.injective Bm (Ideal.primeCompl_le_nonZeroDivisors m)
  refine ⟨(algebraMap K B).injective, fun b => ?_⟩
  obtain ⟨k, hk⟩ := hbij.2 (algebraMap B Bm b)
  refine ⟨k, hinj ?_⟩
  rw [← hk, IsScalarTower.algebraMap_apply K B Bm]

end Base

section Product

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

/-- The spectrum of an algebra isomorphic to the base field is isomorphic to the base. -/
theorem specAlgebra_isIso_of_bijective (h : Function.Bijective (algebraMap K B)) :
    IsIso (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) := by
  change IsIso (Spec.map (CommRingCat.ofHom (algebraMap K B)))
  let e : K ≃+* B := RingEquiv.ofBijective (algebraMap K B) h
  have he : CommRingCat.ofHom (algebraMap K B) = e.toCommRingCatIso.hom := rfl
  rw [he]
  infer_instance

/-- With a base isomorphic to the base field, the second projection is an isomorphism. -/
theorem specFibreProductSnd_isIso_of_bijective (h : Function.Bijective (algebraMap K B)) :
    IsIso (specFibreProductSnd K B Y) := by
  have := specAlgebra_isIso_of_bijective (K := K) (B := B) h
  change IsIso (pullback.snd (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K))
    (Y ↘ Spec (CommRingCat.of K)))
  infer_instance

/-- With a base isomorphic to the base field, every fibre is the inverse of the second projection. -/
theorem specFibreProductSnd_comp_fibre_of_isIso [IsIso (specFibreProductSnd K B Y)]
    (w : B →ₐ[K] K) : specFibreProductSnd K B Y ≫ specFibreProductFibre (V := Y) w = 𝟙 _ := by
  rw [← cancel_mono (specFibreProductSnd K B Y), Category.assoc, specFibreProductFibre_snd,
    Category.comp_id, Category.id_comp]

variable [IsIntegral Y] [IsIntegral (specFibreProduct K B Y)] [Nontrivial B]

/-- **With no base coordinates the product chart has the coordinates of the chart of Y**: the
Jacobian determinant of the second projection between them is 1. -/
theorem chartRelativeJacobianDet_fibreProduct_fin_zero {n : ℕ} (cY : EtaleChart K Y n)
    (φ : MvPolynomial (Fin 0) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale) :
    chartRelativeJacobianDet (K := K) (specFibreProductSnd K B Y) cY
      (fibreProductEtaleChart cY φ hφ) = 1 := by
  classical
  unfold chartRelativeJacobianDet
  have hcoord : ∀ i : Fin n, dominantFunctionFieldAlgHom (K := K) (specFibreProductSnd K B Y)
      (etaleChartFunctionFieldCoords cY (MvPolynomial.X i)) =
        etaleChartFunctionFieldCoords (fibreProductEtaleChart cY φ hφ)
          (MvPolynomial.X (Fin.castAdd 0 i)) := by
    intro i
    change _ = (specFibreProduct K B Y).germToFunctionField _
      (fibreProductCoords cY φ (MvPolynomial.X (Fin.castAdd 0 i)))
    rw [fibreProductCoords_X_castAdd, specFibreProductSectionsEquiv_tmul, map_one, one_mul]
    exact dominantFunctionFieldMap_germ (specFibreProductSnd K B Y) cY.U
      (specFibreProductSnd K B Y ⁻¹ᵁ cY.U) le_rfl _
  have hmat : etaleRelativeJacobian (dominantFunctionFieldAlgHom (K := K)
      (specFibreProductSnd K B Y)) (etaleChartFunctionFieldCoords cY)
      (etaleChartFunctionFieldCoords (fibreProductEtaleChart cY φ hφ))
      (etaleChartFunctionFieldCoords_formallyEtale _) = 1 := by
    ext i j
    simp only [etaleRelativeJacobian, Matrix.of_apply, hcoord, Matrix.one_apply]
    have h := etaleCoordinateDerivation_coordinate
      (etaleChartFunctionFieldCoords (fibreProductEtaleChart cY φ hφ))
      (etaleChartFunctionFieldCoords_formallyEtale _) (Fin.castAdd 0 i) (j : Fin (n + 0))
    refine h.trans ?_
    have hi : (Fin.castAdd 0 i : Fin (n + 0)) = i := Fin.ext rfl
    simp only [hi]
  rw [hmat, Matrix.det_one]

end Product

section Transfer

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {B : Type u} [CommRing B]
  [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] {Y : Scheme.{u}} [IsIntegral Y]
  [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

attribute [local instance] specFibreProduct_isIntegral specFibreProduct_preimage_nonempty

/-- **Restriction to the fibres of a product with a base without coordinates**: a weakly bad
point of the product is a bad point of its fibre, for a klt pair. -/
theorem modelThresholdBadAt_fibre_of_fin_zero {n : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (φ : MvPolynomial (Fin 0) K →ₐ[K] B)
    (hφ : φ.toRingHom.FormallyEtale) (V : Y.Opens) [Nonempty V] {J : Type}
    (g : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) (M : ℕ)
    (w : B →ₐ[K] K) (y : Y)
    (h : ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit fY) d
      (fibreProductPairDivisor D₀) (specFibreProductFibre w y)
      (fun j => (specFibreProduct K B Y).germToFunctionField _ (g j)) M) :
    ModelThresholdBadAt cY fY d D₀ y
      (fun j => Y.germToFunctionField V ((specFibreProductFibre w).appLE _ V
        (specFibreProductFibre_le_preimage w V) (g j))) M := by
  have hbij := algebraMap_bijective_of_formallyEtale_fin_zero φ hφ
  have : IsIso (specFibreProductSnd K B Y) := specFibreProductSnd_isIso_of_bijective hbij
  have hsnd : Function.Bijective (dominantFunctionFieldAlgHom (K := K)
      (specFibreProductSnd K B Y)) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (specFibreProductSnd K B Y)
  have hinv := specFibreProductSnd_comp_fibre_of_isIso (Y := Y) w
  apply modelThresholdBadAt_of_modelThresholdWeakBadAt_of_klt cY fY hd D₀ hklt
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hye, hineq⟩ := h
  have hσY := dominantFunctionFieldAlgHom_comp_bijective (specFibreProductSnd K B Y) σ hsnd hσ
  refine ⟨U, hUi, hUn, hUo, hUs, σ ≫ specFibreProductSnd K B Y, inferInstance, inferInstance,
    hσY, cU, e, ?_, ?_⟩
  · have h1 : specFibreProductSnd K B Y (specFibreProductFibre w y) ∈
        closure ({specFibreProductSnd K B Y (σ (e : U))} : Set Y) :=
      map_mem_closure (specFibreProductSnd K B Y).continuous hye fun z hz => by
        rw [Set.mem_singleton_iff.mp hz]
        rfl
    have h2 : specFibreProductSnd K B Y (specFibreProductFibre w y) = y := by
      rw [← Scheme.Hom.comp_apply, specFibreProductFibre_snd]
      rfl
    rw [h2] at h1
    rw [Scheme.Hom.comp_apply]
    exact h1
  · intro j hj
    -- the pulled back member is the member of the product
    have hpull : (dominantFunctionFieldMap (specFibreProductSnd K B Y)).hom
        (Y.germToFunctionField V ((specFibreProductFibre w).appLE _ V
          (specFibreProductFibre_le_preimage w V) (g j))) =
        (specFibreProduct K B Y).germToFunctionField _ (g j) := by
      have hsec : (specFibreProductSnd K B Y).appLE V (specFibreProductSnd K B Y ⁻¹ᵁ V) le_rfl
          ((specFibreProductFibre w).appLE _ V (specFibreProductFibre_le_preimage w V) (g j)) =
            g j := by
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hinv,
          id_appLE_self]
      rw [dominantFunctionFieldMap_germ (specFibreProductSnd K B Y) V
        (specFibreProductSnd K B Y ⁻¹ᵁ V) le_rfl, hsec]
    have hj' : (specFibreProduct K B Y).germToFunctionField _ (g j) ≠ 0 := by
      rw [← hpull]
      exact (map_ne_zero_iff _ hsnd.1).mpr hj
    have hb := hineq j hj'
    -- the log discrepancies agree
    have hcomp := logDiscrepancyDivisor_comp (specFibreProductSnd K B Y) σ hsnd hσ cY fY d D₀
      (fibreProductEtaleChart cY φ hφ) cU etaleCharts_cover
    have hunit : crepantPullbackFormUnit (specFibreProductSnd K B Y) hsnd cY fY
        (fibreProductEtaleChart cY φ hφ) = fibreProductPairUnit fY := by
      unfold crepantPullbackFormUnit fibreProductPairUnit
      apply Units.ext
      rw [Units.val_mul, IsUnit.unit_spec, chartRelativeJacobianDet_fibreProduct_fin_zero,
        mul_one]
    rw [hcomp, hunit]
    have hord : U.ord ((dominantFunctionFieldMap (σ ≫ specFibreProductSnd K B Y)).hom
        (Y.germToFunctionField V ((specFibreProductFibre w).appLE _ V
          (specFibreProductFibre_le_preimage w V) (g j)))) (e : U) =
        U.ord ((dominantFunctionFieldMap σ).hom
          ((specFibreProduct K B Y).germToFunctionField _ (g j))) (e : U) := by
      rw [← hpull]
      change U.ord (dominantFunctionFieldAlgHom (K := K) (σ ≫ specFibreProductSnd K B Y) _) _ =
        U.ord (dominantFunctionFieldAlgHom (K := K) σ
          (dominantFunctionFieldAlgHom (K := K) (specFibreProductSnd K B Y) _)) _
      rw [dominantFunctionFieldAlgHom_comp, AlgHom.comp_apply]
    rw [hord]
    exact hb

end Transfer

end MixedFujita
