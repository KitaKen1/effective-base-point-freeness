/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProductChartJacobian
public import MixedFujita.KltLemmaThreeFromSpecialization
public import MixedFujita.WeakModelThresholdBad

/-!
The product of a klt pair with a smooth affine variety with global étale coordinates, and the
restriction statements for it (step 15).

For a K-scheme Y with a pair (c_Y, f_Y, d, D₀) and a domain B of finite type with formally étale
coordinates φ : K[u] → B, the product pair on P = Spec B ×_K Y has the product chart
(`fibreProductEtaleChart`), the pulled back form unit (`fibreProductPairUnit`) and the pulled back
divisor (`fibreProductPairDivisor`); the fibre of P over a K-point w of B is the morphism
Y → P, y ↦ (w, y) (`specFibreProductFibre`). Families live on the inverse images of affine opens
V of Y, whose functions are B ⊗_K Γ(V). The two statements below are what the specialization of
bad points in smooth families (`KltFamilySpecializationStatement`) needs from the product, in the
form of check 309, with badness on the product in the weak model form
(`ModelThresholdWeakBadAt`, no positivity of the log discrepancy), for which Lemma 3 for a fixed
family holds for every pair, so that the product pair need not be shown klt:

* `KltProductGenericRestrictionStatement`: over a dense open of Spec B, a bad point of the fibre
  is a weakly bad point of the product (generic restriction);
* `KltProductFibreRestrictionStatement`: a weakly bad point of the product is a bad point of its
  fibre (restriction to fibres, the inversion of adjunction direction).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra
  specFibreProductOverAlgebra specFibreProductOverField specFibreProductSnd_isDominant
  specFibreProductSnd_isOver

section ProductPair

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {V : Scheme.{u}}
  [V.Over (Spec (CommRingCat.of K))]

/-- The spectrum of a K-algebra of finite type is locally of finite type over K. -/
theorem specAlgebra_locallyOfFiniteType [Algebra.FiniteType K B] :
    LocallyOfFiniteType (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K B)))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The fibre product of the spectrum of a domain of finite type over an algebraically closed field
with an integral locally noetherian scheme is integral. -/
theorem specFibreProduct_isIntegral [IsAlgClosed K] [IsDomain B] [Algebra.FiniteType K B]
    [IsIntegral V] [IsLocallyNoetherian V] : IsIntegral (specFibreProduct K B V) := by
  have := specAlgebra_locallyOfFiniteType (K := K) (B := B)
  exact isIntegral_pullback_of_isAffine _ _

variable [IsIntegral V] [IsIntegral (specFibreProduct K B V)] [Nontrivial B]

/-- The form unit of the product pair: the pullback of the form unit of V. -/
noncomputable def fibreProductPairUnit (fV : V.functionFieldˣ) :
    (specFibreProduct K B V).functionFieldˣ :=
  Units.map (dominantFunctionFieldMap (specFibreProductSnd K B V)).hom.toMonoidHom fV

/-- The divisor of the product pair: the pullback of the divisor of V. -/
noncomputable def fibreProductPairDivisor (DV : CartierDivisor V) :
    CartierDivisor (specFibreProduct K B V) :=
  cartierPullback (specFibreProductSnd K B V) DV

end ProductPair

section Fibre

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {V : Scheme.{u}}
  [V.Over (Spec (CommRingCat.of K))]

/-- The fibre of Spec B ×_K V over a K-point w of B: the morphism V → Spec B ×_K V, y ↦ (w, y). -/
noncomputable def specFibreProductFibre (w : B →ₐ[K] K) : V ⟶ specFibreProduct K B V :=
  pullback.lift ((V ↘ Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom w.toRingHom))
    (𝟙 V) (by
      change ((V ↘ Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom w.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 V ≫ (V ↘ Spec (CommRingCat.of K))
      rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : w.toRingHom.comp (algebraMap K B) = RingHom.id K := by
        ext k
        exact w.commutes k
      rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp])

theorem specFibreProductFibre_snd (w : B →ₐ[K] K) :
    specFibreProductFibre (V := V) w ≫ specFibreProductSnd K B V = 𝟙 V :=
  pullback.lift_snd _ _ _

end Fibre

section Preimage

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

/-- The inverse image of a nonempty open of Y in Spec B ×_K Y is nonempty. -/
theorem specFibreProduct_preimage_nonempty [Nontrivial B] (V : Y.Opens) [Nonempty V] :
    Nonempty (specFibreProductSnd K B Y ⁻¹ᵁ V) := by
  have : Surjective (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) :=
    specMap_algebraMap_surjective
  obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty V)
  obtain ⟨p, hp⟩ := (specFibreProductSnd K B Y).surjective y
  exact ⟨⟨p, show specFibreProductSnd K B Y p ∈ V from hp ▸ hy⟩⟩

/-- The fibre over a K-point maps an open of Y into the inverse image of the open. -/
theorem specFibreProductFibre_le_preimage (w : B →ₐ[K] K) (V : Y.Opens) :
    V ≤ specFibreProductFibre (V := Y) w ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ V) := by
  intro y hy
  change specFibreProductSnd K B Y (specFibreProductFibre (V := Y) w y) ∈ V
  rw [← Scheme.Hom.comp_apply, specFibreProductFibre_snd]
  exact hy

end Preimage

section Statements

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

attribute [local instance] specFibreProduct_isIntegral specFibreProduct_preimage_nonempty

/-- **Generic restriction for the product**: for a klt pair with effective boundary on a normal
variety Y whose codimension-one points lie in étale charts, a domain B of finite type with
formally étale coordinates, an affine open V of Y and a family g of functions on its inverse image
in Spec B ×_K Y, not all zero, there is a nonzero h ∈ B such that over every K-point w of B with w h ≠ 0, a
closed point y of V at which the restriction of g to the fibre over w has threshold at most 1/M
gives the point (w, y) of the product at which g has threshold at most 1/M in the weak model
form. -/
def KltProductGenericRestrictionStatement : Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (n : ℕ), 1 ≤ n →
    (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered n K Y →
    ∀ (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
    ∀ D₀ : CartierDivisor Y, LogPairBoundaryEffective cY fY d D₀ → LogPairIsKlt cY fY d D₀ →
    ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (e : ℕ)
      (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
      (V : Y.Opens), IsAffineOpen V → ∀ [Nonempty V] {J : Type} [Finite J]
      (g : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) (M : ℕ), 1 ≤ M →
      (∃ j, (specFibreProduct K B Y).germToFunctionField _ (g j) ≠ 0) →
      ∃ h : B, h ≠ 0 ∧ ∀ w : B →ₐ[K] K, w h ≠ 0 → ∀ y : Y, y ∈ V → IsClosed ({y} : Set Y) →
        ModelThresholdBadAt cY fY d D₀ y
          (fun j => Y.germToFunctionField V ((specFibreProductFibre w).appLE _ V
            (specFibreProductFibre_le_preimage w V) (g j))) M →
        ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit fY) d
          (fibreProductPairDivisor D₀) (specFibreProductFibre w y)
          (fun j => (specFibreProduct K B Y).germToFunctionField _ (g j)) M

/-- **Restriction to the fibres of the product** (the inversion of adjunction direction): in the
situation of `KltProductGenericRestrictionStatement`, if a family g of functions on the inverse
image of an affine open V of Y has threshold at most 1/M at the point (w, y) of the product in
the weak model form, then its restriction to the fibre over w has threshold at most 1/M at y. -/
def KltProductFibreRestrictionStatement : Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ), 1 ≤ n →
    (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered n K Y →
    ∀ (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
    ∀ D₀ : CartierDivisor Y, LogPairBoundaryEffective cY fY d D₀ → LogPairIsKlt cY fY d D₀ →
    ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (e : ℕ)
      (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
      (V : Y.Opens), IsAffineOpen V → ∀ [Nonempty V] {J : Type} [Finite J]
      (g : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) (M : ℕ), 1 ≤ M →
      ∀ (w : B →ₐ[K] K) (y : Y), y ∈ V → IsClosed ({y} : Set Y) →
        ModelThresholdWeakBadAt (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit fY) d
          (fibreProductPairDivisor D₀) (specFibreProductFibre w y)
          (fun j => (specFibreProduct K B Y).germToFunctionField _ (g j)) M →
        ModelThresholdBadAt cY fY d D₀ y
          (fun j => Y.germToFunctionField V ((specFibreProductFibre w).appLE _ V
            (specFibreProductFibre_le_preimage w V) (g j))) M

end Statements

end MixedFujita
