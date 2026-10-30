/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import SGA.Foundations.Cohomology.CechLocalization
public import SGA.Foundations.Cohomology.CechComparison
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-! A boundary after localization descends after multiplication by one
denominator. For a finite Cech cover, localization of section modules gives
localization of cochains; a single denominator handles the whole cochain.
This supplies the algebraic step for descending locally vanishing classes. -/

@[expose] public section
open CategoryTheory TopologicalSpace Opposite TopCat.Presheaf
namespace MixedFujita
universe u v

theorem localized_boundary_exists_denominator
    {R : Type*} [CommRing R] (S : Submonoid R)
    {M₀ M₁ N₀ N₁ : Type*}
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup N₀] [AddCommGroup N₁]
    [Module R M₀] [Module R M₁] [Module R N₀] [Module R N₁]
    (f₀ : M₀ →ₗ[R] N₀) (f₁ : M₁ →ₗ[R] N₁)
    [IsLocalizedModule S f₀] [IsLocalizedModule S f₁]
    (d : M₀ →ₗ[R] M₁) (d' : N₀ →ₗ[R] N₁)
    (hcomm : ∀ b, f₁ (d b) = d' (f₀ b))
    (c : M₁) (b' : N₀) (hb' : d' b' = f₁ c) :
    ∃ (s : S) (b : M₀), d b = (s : R) • c := by
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalizedModule.surj S f₀ b'
  have he : f₁ (d b) = f₁ ((s : R) • c) := by
    rw [hcomm, ← hs]
    simp only [Submonoid.smul_def, map_smul, hb']
  obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) he
  refine ⟨t * s, (t : R) • b, ?_⟩
  simpa only [Submonoid.smul_def, map_smul, Submonoid.coe_mul, mul_smul] using ht

variable {R : Type v} [CommRing R] {X : TopCat.{u}}
  (P Q : X.Presheaf AddCommGrpCat.{v})
  [∀ V : Opens X, Module R (P.obj (op V))]
  [∀ V : Opens X, Module R (Q.obj (op V))]
  (φ : P ⟶ Q)
  (hφ : ∀ (V : Opens X) (r : R) (s : P.obj (op V)), φ.app (op V) (r • s) = r • φ.app (op V) s)

noncomputable def presheafLinearApp (V : Opens X) : P.obj (op V) →ₗ[R] Q.obj (op V) where
  toFun := φ.app (op V)
  map_add' := map_add _
  map_smul' := hφ V

noncomputable def cechCochainLinearMap {ι : Type*} (U : ι → Opens X) (p : ℕ) :
    CechCochain U P p →ₗ[R] CechCochain U Q p :=
  LinearMap.pi fun i ↦ presheafLinearApp P Q φ hφ (cechOpen U i) ∘ₗ LinearMap.proj i

theorem finite_cechCochainLinearMap_isLocalizedModule
    {ι : Type*} [Finite ι] (U : ι → Opens X) (S : Submonoid R) (p : ℕ)
    (hloc : ∀ i : Fin (p + 1) → ι,
      IsLocalizedModule S (presheafLinearApp P Q φ hφ (cechOpen U i))) :
    IsLocalizedModule S (cechCochainLinearMap P Q φ hφ U p) := by
  let := hloc
  exact IsLocalizedModule.pi S (fun i ↦ presheafLinearApp P Q φ hφ (cechOpen U i))

theorem finite_cech_boundary_exists_denominator
    {ι : Type*} [Finite ι] (U : ι → Opens X) (S : Submonoid R)
    (hP : ∀ ⦃V W : Opens X⦄ (h : W ≤ V) (r : R) (s : P.obj (op V)),
      P.map (homOfLE h).op (r • s) = r • P.map (homOfLE h).op s)
    (hQ : ∀ ⦃V W : Opens X⦄ (h : W ≤ V) (r : R) (s : Q.obj (op V)),
      Q.map (homOfLE h).op (r • s) = r • Q.map (homOfLE h).op s)
    (p : ℕ)
    (hloc : ∀ m : ℕ, ∀ i : Fin (m + 1) → ι,
      IsLocalizedModule S (presheafLinearApp P Q φ hφ (cechOpen U i)))
    (c : CechCochain U P (p + 1)) (b' : CechCochain U Q p)
    (hb' : cechD U Q p b' = cechCochainMap U φ (p + 1) c) :
    ∃ (s : S) (b : CechCochain U P p), cechD U P p b = (s : R) • c := by
  let := finite_cechCochainLinearMap_isLocalizedModule P Q φ hφ U S p (hloc p)
  let := finite_cechCochainLinearMap_isLocalizedModule P Q φ hφ U S (p + 1) (hloc (p + 1))
  exact localized_boundary_exists_denominator S
    (cechCochainLinearMap P Q φ hφ U p) (cechCochainLinearMap P Q φ hφ U (p + 1))
    (cechDₗ P hP U p) (cechDₗ Q hQ U p)
    (fun b ↦ (cechD_cechCochainMap U φ b).symm) c b' hb'

theorem finite_cech_cocycle_exists_denominator_of_target_exact
    {ι : Type*} [Finite ι] (U : ι → Opens X) (S : Submonoid R)
    (hP : ∀ ⦃V W : Opens X⦄ (h : W ≤ V) (r : R) (s : P.obj (op V)),
      P.map (homOfLE h).op (r • s) = r • P.map (homOfLE h).op s)
    (hQ : ∀ ⦃V W : Opens X⦄ (h : W ≤ V) (r : R) (s : Q.obj (op V)),
      Q.map (homOfLE h).op (r • s) = r • Q.map (homOfLE h).op s)
    (p : ℕ)
    (hloc : ∀ m : ℕ, ∀ i : Fin (m + 1) → ι,
      IsLocalizedModule S (presheafLinearApp P Q φ hφ (cechOpen U i)))
    (hex : (cechComplex U Q).ExactAt (p + 1))
    (c : CechCochain U P (p + 1)) (hc : cechD U P (p + 1) c = 0) :
    ∃ (s : S) (b : CechCochain U P p), cechD U P p b = (s : R) • c := by
  rw [cechComplex_exactAt_succ_iff] at hex
  obtain ⟨b', hb'⟩ := hex (cechCochainMap U φ (p + 1) c) (by
    rw [cechD_cechCochainMap, hc, map_zero])
  exact finite_cech_boundary_exists_denominator P Q φ hφ U S hP hQ p hloc c b' hb'

end MixedFujita
