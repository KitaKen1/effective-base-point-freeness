/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltHypersurfaceStep

/-!
Weak badness on an open sub-product with shifted coordinates (step 15, the klt restriction theorem).

Let θ : B → B' be a K-algebra map with Spec B' → Spec B an open immersion (a localization), and
let the étale coordinates φ' of B' be the images of the coordinates φ of B up to constants:
θ(φ(X_i)) = φ'(X_i) + c_i. The map of products Spec B' ×_K Y → Spec B ×_K Y is an open immersion
along which the Jacobian of the product charts is one, so the pulled back product pair is the
product pair of B'. Hence weak badness of a family at (w' ∘ θ, y) on the product for B gives weak
badness of the pulled back family at (w', y) on the product for B'
(`modelThresholdWeakBadAt_fibreProduct_shift`). This is used to translate a coordinate to vanish
at w and to localize B so that the hyperplane through w is integral.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Jacobian

variable {K R S : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] {n : ℕ}

/-- The Jacobian of coordinates which are shifted by constants is one. -/
theorem etaleRelativeJacobian_eq_one_of_shift (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (c : Fin n → K)
    (h : ∀ i, ψ (x (MvPolynomial.X i)) = y (MvPolynomial.X i) + algebraMap K S (c i)) :
    etaleRelativeJacobian ψ x y hy = 1 := by
  ext i j
  simp only [etaleRelativeJacobian, Matrix.of_apply, h i, map_add, Derivation.map_algebraMap,
    add_zero, etaleCoordinateDerivation_coordinate, Matrix.one_apply]

end Jacobian

section Shift

variable {K : Type u} [Field K] {B B' : Type u} [CommRing B] [CommRing B'] [Algebra K B]
  [Algebra K B'] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] specAlgebraOver structureSectionsAlgebra specFibreProductOverAlgebra
  specFibreProductOverField specFibreProduct_isScalarTower

/-- The map of products of an open immersion of spectra is an open immersion. -/
theorem specFibreProductMap_isOpenImmersion (θ : B →ₐ[K] B')
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom))] :
    IsOpenImmersion (specFibreProductMap (Y := Y) θ) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom)))
    (inferInstance : IsOpenImmersion (𝟙 Y)) (specMap_algHom_comp_over θ) (Category.id_comp _).symm

/-- The map of products is a morphism over K. -/
theorem specFibreProductMap_isOver (θ : B →ₐ[K] B') :
    (specFibreProductMap (Y := Y) θ).IsOver (Spec (CommRingCat.of K)) := by
  constructor
  change specFibreProductMap θ ≫ specFibreProductFst K B Y ≫
    (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) =
      specFibreProductFst K B' Y ≫ (Spec (CommRingCat.of B') ↘ Spec (CommRingCat.of K))
  rw [← Category.assoc, specFibreProductMap_fst, Category.assoc, ← specMap_algHom_comp_over θ]

variable {n e : ℕ} [Nontrivial B] [Nontrivial B']

/-- **The product charts of shifted coordinates have Jacobian one** along the map of products. -/
theorem chartRelativeJacobianDet_fibreProductMap_shift [IsIntegral (specFibreProduct K B Y)]
    [IsIntegral (specFibreProduct K B' Y)] (θ : B →ₐ[K] B')
    [IsDominant (specFibreProductMap (Y := Y) θ)]
    [(specFibreProductMap (Y := Y) θ).IsOver (Spec (CommRingCat.of K))]
    (cY : EtaleChart K Y n) (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
    (φ' : MvPolynomial (Fin e) K →ₐ[K] B') (hφ' : φ'.toRingHom.FormallyEtale) (c : Fin e → K)
    (hθ : ∀ l, θ (φ (MvPolynomial.X l)) = φ' (MvPolynomial.X l) + algebraMap K B' (c l)) :
    chartRelativeJacobianDet (specFibreProductMap (Y := Y) θ) (fibreProductEtaleChart cY φ hφ)
      (fibreProductEtaleChart cY φ' hφ') = 1 := by
  unfold chartRelativeJacobianDet
  rw [etaleRelativeJacobian_eq_one_of_shift _ _ _ _ (Fin.addCases (fun _ => 0) c), Matrix.det_one]
  intro a
  have hV' : specFibreProductSnd K B' Y ⁻¹ᵁ cY.U ≤ specFibreProductMap (Y := Y) θ ⁻¹ᵁ
      (specFibreProductSnd K B Y ⁻¹ᵁ cY.U) := fun x hx => by
    change (specFibreProductMap θ ≫ specFibreProductSnd K B Y) x ∈ cY.U
    rw [specFibreProductMap_snd]
    exact hx
  have : Nonempty (specFibreProductSnd K B Y ⁻¹ᵁ cY.U) := (fibreProductEtaleChart cY φ hφ).nonempty
  have : Nonempty (specFibreProductSnd K B' Y ⁻¹ᵁ cY.U) :=
    (fibreProductEtaleChart cY φ' hφ').nonempty
  change (dominantFunctionFieldMap (specFibreProductMap (Y := Y) θ)).hom
      ((specFibreProduct K B Y).germToFunctionField _
        (fibreProductCoords cY φ (MvPolynomial.X a))) =
    (specFibreProduct K B' Y).germToFunctionField _ (fibreProductCoords cY φ' (MvPolynomial.X a)) +
      algebraMap K _ (Fin.addCases (fun _ => 0) c a)
  rw [dominantFunctionFieldMap_germ _ _ _ hV']
  refine Fin.addCases (fun j => ?_) (fun l => ?_) a
  · rw [Fin.addCases_left, map_zero, add_zero, fibreProductCoords_X_castAdd,
      fibreProductCoords_X_castAdd, specFibreProductSectionsEquiv_tmul,
      specFibreProductSectionsEquiv_tmul, map_one, map_one, one_mul, one_mul]
    congr 1
    exact specFibreProductMap_appLE_snd θ cY.U _
  · rw [Fin.addCases_right, fibreProductCoords_X_natAdd, fibreProductCoords_X_natAdd,
      specFibreProductSectionsEquiv_tmul, specFibreProductSectionsEquiv_tmul, map_one, map_one,
      mul_one, mul_one, specFibreProductMap_appLE_algebraMap, hθ l, map_add, map_add,
      ← IsScalarTower.algebraMap_apply]
    congr 1
    exact (sectionGermAlgHom (K := K) (specFibreProductSnd K B' Y ⁻¹ᵁ cY.U)).commutes (c l)

end Shift

section Transport

variable {K : Type u} [Field K] [IsAlgClosed K] {B B' : Type u} [CommRing B] [IsDomain B]
  [Algebra K B] [Algebra.FiniteType K B] [CommRing B'] [IsDomain B'] [Algebra K B']
  [Algebra.FiniteType K B'] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] {n e : ℕ}

attribute [local instance] specAlgebraOver structureSectionsAlgebra specFibreProductOverAlgebra
  specFibreProductOverField specFibreProduct_isScalarTower specFibreProduct_isIntegral
  specFibreProduct_preimage_nonempty specFibreProductSnd_isDominant specFibreProductSnd_isOver

set_option maxHeartbeats 1600000 in
/-- **Weak badness on an open sub-product with shifted coordinates.** -/
theorem modelThresholdWeakBadAt_fibreProduct_shift (θ : B →ₐ[K] B')
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom))]
    [IsDominant (specFibreProductMap (Y := Y) θ)]
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
    (φ' : MvPolynomial (Fin e) K →ₐ[K] B') (hφ' : φ'.toRingHom.FormallyEtale) (c : Fin e → K)
    (hθ : ∀ l, θ (φ (MvPolynomial.X l)) = φ' (MvPolynomial.X l) + algebraMap K B' (c l))
    (w' : B' →ₐ[K] K) (y : Y) {J : Type*} (gP : J → (specFibreProduct K B Y).functionField)
    (M : ℕ)
    (h : ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY)
      d (fibreProductPairDivisor (K := K) (B := B) D₀) (specFibreProductFibre (V := Y) (w'.comp θ) y)
      gP M) :
    ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ' hφ') (fibreProductPairUnit (K := K) fY)
      d (fibreProductPairDivisor (K := K) (B := B') D₀) (specFibreProductFibre (V := Y) w' y)
      (fun k => (dominantFunctionFieldMap (specFibreProductMap (Y := Y) θ)).hom (gP k)) M := by
  haveI := specFibreProductMap_isOpenImmersion (Y := Y) θ
  haveI := specFibreProductMap_isOver (Y := Y) θ
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K)
      (specFibreProductMap (Y := Y) θ)) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion _
  have hpt : specFibreProductMap (Y := Y) θ (specFibreProductFibre (V := Y) w' y) =
      specFibreProductFibre (V := Y) (w'.comp θ) y := by
    have h1 := congrArg (fun f : Y ⟶ specFibreProduct K B Y => f y)
      (specFibreProductFibre_comp_map (Y := Y) θ w')
    simp only [Scheme.Hom.comp_apply] at h1
    exact h1
  rw [← hpt] at h
  have h2 := modelThresholdWeakBadAt_openImmersion_pullback (specFibreProductMap (Y := Y) θ) hj
    (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
    (fibreProductPairDivisor (K := K) (B := B) D₀) (fibreProductEtaleChart cY φ' hφ')
    (specFibreProductFibre (V := Y) w' y) gP _ (fun k => rfl) M h
  have hunit : crepantPullbackFormUnit (specFibreProductMap (Y := Y) θ) hj
      (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY)
      (fibreProductEtaleChart cY φ' hφ') = fibreProductPairUnit (K := K) fY := by
    apply Units.ext
    simp only [crepantPullbackFormUnit, Units.val_mul, Units.coe_map, IsUnit.unit_spec,
      fibreProductPairUnit]
    rw [chartRelativeJacobianDet_fibreProductMap_shift θ cY φ hφ φ' hφ' c hθ, mul_one]
    change dominantFunctionFieldAlgHom (K := K) (specFibreProductMap θ)
        (dominantFunctionFieldAlgHom (K := K) (specFibreProductSnd K B Y) (fY : Y.functionField)) =
      dominantFunctionFieldAlgHom (K := K) (specFibreProductSnd K B' Y) (fY : Y.functionField)
    rw [← AlgHom.comp_apply, ← dominantFunctionFieldAlgHom_comp,
      dominantFunctionFieldAlgHom_congr_hom (specFibreProductMap_snd θ)]
  have hdiv : cartierPullback (specFibreProductMap (Y := Y) θ)
      (fibreProductPairDivisor (K := K) (B := B) D₀) =
      fibreProductPairDivisor (K := K) (B := B') D₀ := by
    change cartierPullback (specFibreProductMap θ) (cartierPullback (specFibreProductSnd K B Y) D₀) =
      cartierPullback (specFibreProductSnd K B' Y) D₀
    rw [← cartierPullback_comp]
    congr 1
    exact specFibreProductMap_snd θ
  rwa [hunit, hdiv] at h2

end Transport

end MixedFujita
