/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineSectionsBaseChange
public import MixedFujita.TensorEtaleCoordinates
public import MixedFujita.AffineEtaleChartModel

/-!
Étale charts of the fibre product of a scheme with the spectrum of an algebra with global étale
coordinates (step 15).

For a K-scheme T and a K-algebra B, the fibre product P = Spec B ×_K T is a scheme over Spec B
through the first projection and over K through Spec B. Over an affine open U of T the functions on
the inverse image of U are B ⊗_K Γ(T, U) (the affine base change `sectionsBaseChangeEquiv`), and
the K-algebra structure of the functions of P is the one through B
(`specFibreProduct_isScalarTower`). If T has an étale chart c with coordinates z and B has formally
étale coordinates u : K[u] → B, then K[z, u] → B[z] is formally étale (the base change of K[u] → B
along K[u] → K[u][z]) and B[z] → B ⊗_K Γ(T, U) is formally étale (`formallyEtale_tensorCoordinates`),
so the inverse image of c.U carries the étale chart with coordinates (z, u)
(`fibreProductEtaleChart`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra structureSectionsAlgebra

section FibreProduct

variable (K : Type u) [Field K] (B : Type u) [CommRing B] [Algebra K B] (T : Scheme.{u})
  [T.Over (Spec (CommRingCat.of K))]

/-- The fibre product Spec B ×_K T. -/
noncomputable abbrev specFibreProduct : Scheme.{u} :=
  pullback (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) (T ↘ Spec (CommRingCat.of K))

/-- The first projection Spec B ×_K T → Spec B. -/
noncomputable abbrev specFibreProductFst : specFibreProduct K B T ⟶ Spec (CommRingCat.of B) :=
  pullback.fst (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) (T ↘ Spec (CommRingCat.of K))

/-- The second projection Spec B ×_K T → T. -/
noncomputable abbrev specFibreProductSnd : specFibreProduct K B T ⟶ T :=
  pullback.snd (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) (T ↘ Spec (CommRingCat.of K))

/-- The fibre product over Spec B, through the first projection. -/
@[instance_reducible]
noncomputable def specFibreProductOverAlgebra :
    (specFibreProduct K B T).Over (Spec (CommRingCat.of B)) :=
  ⟨specFibreProductFst K B T⟩

/-- The fibre product over K, through Spec B. -/
@[instance_reducible]
noncomputable def specFibreProductOverField :
    (specFibreProduct K B T).Over (Spec (CommRingCat.of K)) :=
  ⟨specFibreProductFst K B T ≫ (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K))⟩

attribute [local instance] specFibreProductOverAlgebra specFibreProductOverField

/-- The fibre product is a pullback square over K, with the second projection to T. -/
theorem specFibreProduct_isPullback :
    IsPullback (specFibreProductSnd K B T) (specFibreProduct K B T ↘ Spec (CommRingCat.of B)) (T ↘ Spec (CommRingCat.of K))
      (Spec.map (CommRingCat.ofHom (algebraMap K B))) :=
  (IsPullback.of_hasPullback _ _).flip

/-- The K-algebra structure of the functions of the fibre product is the one through B. -/
theorem specFibreProduct_algebraMap (W : (specFibreProduct K B T).Opens) (k : K) :
    algebraMap K Γ(specFibreProduct K B T, W) k =
      algebraMap B Γ(specFibreProduct K B T, W) (algebraMap K B k) := by
  change ((specFibreProduct K B T).baseRingToStructurePresheaf K).app (op W) k =
    ((specFibreProduct K B T).baseRingToStructurePresheaf B).app (op W) (algebraMap K B k)
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE,
    Scheme.baseRingToStructurePresheaf_app_eq_appLE]
  change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (specFibreProductFst K B T ≫ Spec.map (CommRingCat.ofHom (algebraMap K B))).appLE ⊤ W
        le_top) k =
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (specFibreProductFst K B T).appLE ⊤ W le_top)
      (algebraMap K B k)
  rw [Scheme.Hom.comp_appLE, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

/-- The scalar tower K → B → Γ(P, W) of the fibre product. -/
theorem specFibreProduct_isScalarTower (W : (specFibreProduct K B T).Opens) :
    IsScalarTower K B Γ(specFibreProduct K B T, W) :=
  IsScalarTower.of_algebraMap_eq fun k => specFibreProduct_algebraMap K B T W k

end FibreProduct

section Chart

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {T : Scheme.{u}}
  [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] specFibreProductOverAlgebra specFibreProductOverField
  specFibreProduct_isScalarTower

/-- The functions on the inverse image of an affine open U of T in the fibre product are
B ⊗_K Γ(T, U). -/
noncomputable def specFibreProductSectionsEquiv {U : T.Opens} (hU : IsAffineOpen U) :
    B ⊗[K] Γ(T, U) ≃ₐ[B] Γ(specFibreProduct K B T, specFibreProductSnd K B T ⁻¹ᵁ U) :=
  sectionsBaseChangeEquiv (specFibreProduct_isPullback K B T) hU

theorem specFibreProductSectionsEquiv_tmul {U : T.Opens} (hU : IsAffineOpen U) (b : B)
    (a : Γ(T, U)) :
    specFibreProductSectionsEquiv hU (b ⊗ₜ a) =
      algebraMap B Γ(specFibreProduct K B T, specFibreProductSnd K B T ⁻¹ᵁ U) b *
        (specFibreProductSnd K B T).appLE U (specFibreProductSnd K B T ⁻¹ᵁ U) le_rfl a :=
  sectionsBaseChangeEquiv_tmul (specFibreProduct_isPullback K B T) hU b a

variable {n e : ℕ}

/-- The variables z_1, …, z_n, u_1, …, u_e of K[z, u] as variables of K[u][z]. -/
noncomputable def productVariablesEquiv (K : Type u) [Field K] (n e : ℕ) :
    MvPolynomial (Fin (n + e)) K ≃ₐ[K] MvPolynomial (Fin n) (MvPolynomial (Fin e) K) :=
  (MvPolynomial.renameEquiv K finSumFinEquiv.symm).trans (MvPolynomial.sumAlgEquiv K (Fin n) (Fin e))

theorem productVariablesEquiv_X_castAdd (j : Fin n) :
    productVariablesEquiv K n e (MvPolynomial.X (Fin.castAdd e j)) = MvPolynomial.X j := by
  simp [productVariablesEquiv, MvPolynomial.sumAlgEquiv_X_inl]

theorem productVariablesEquiv_X_natAdd (l : Fin e) :
    productVariablesEquiv K n e (MvPolynomial.X (Fin.natAdd n l)) =
      MvPolynomial.C (MvPolynomial.X l) := by
  simp [productVariablesEquiv, MvPolynomial.sumAlgEquiv_X_inr]

end Chart

section ChartConstruction

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {T : Scheme.{u}}
  [T.Over (Spec (CommRingCat.of K))] {n e : ℕ}

attribute [local instance] specFibreProductOverAlgebra specFibreProductOverField
  specFibreProduct_isScalarTower

/-- The coordinates (z, u) of the fibre product over the inverse image of an étale chart. -/
noncomputable def fibreProductCoords (c : EtaleChart K T n)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) :
    MvPolynomial (Fin (n + e)) K →ₐ[K]
      Γ(specFibreProduct K B T, specFibreProductSnd K B T ⁻¹ᵁ c.U) :=
  MvPolynomial.aeval fun i => specFibreProductSectionsEquiv c.isAffine
    (Fin.addCases (fun j => (1 : B) ⊗ₜ[K] c.coords (MvPolynomial.X j))
      (fun l => φ (MvPolynomial.X l) ⊗ₜ[K] (1 : Γ(T, c.U))) i)

theorem fibreProductCoords_X_castAdd (c : EtaleChart K T n)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (j : Fin n) :
    fibreProductCoords c φ (MvPolynomial.X (Fin.castAdd e j)) =
      specFibreProductSectionsEquiv c.isAffine ((1 : B) ⊗ₜ[K] c.coords (MvPolynomial.X j)) := by
  simp [fibreProductCoords]

theorem fibreProductCoords_X_natAdd (c : EtaleChart K T n)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (l : Fin e) :
    fibreProductCoords c φ (MvPolynomial.X (Fin.natAdd n l)) =
      specFibreProductSectionsEquiv c.isAffine (φ (MvPolynomial.X l) ⊗ₜ[K] (1 : Γ(T, c.U))) := by
  simp [fibreProductCoords]

/-- The coordinates of the fibre product are formally étale: they factor as
K[z, u] ≅ K[u][z] → K[u] ⊗ Γ(U) → B ⊗ Γ(U) ≅ Γ(P, U'), where the middle maps are the tensor
coordinates and the base change of K[u] → B. -/
theorem fibreProductCoords_formallyEtale (c : EtaleChart K T n)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale) :
    (fibreProductCoords c φ).toRingHom.FormallyEtale := by
  classical
  -- the algebra structures given by the coordinates
  let _ : Algebra (MvPolynomial (Fin e) K) B := φ.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin e) K) B :=
    IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  let _ : Algebra (MvPolynomial (Fin n) K) Γ(T, c.U) := c.coords.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) Γ(T, c.U) :=
    IsScalarTower.of_algebraMap_eq fun k => (c.coords.commutes k).symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin e) K) B := RingHom.formallyEtale_algebraMap.mp hφ
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) K) Γ(T, c.U) :=
    RingHom.formallyEtale_algebraMap.mp c.formallyEtale
  -- (i) the tensor coordinates K[u][z] → K[u] ⊗ Γ(U)
  let Tc := tensorCoordinates K (MvPolynomial (Fin e) K) Γ(T, c.U) n
  have h1 : Tc.toRingHom.FormallyEtale := by
    let _ := tensorCoordinatesAlgebra K (MvPolynomial (Fin e) K) Γ(T, c.U) n
    have h : Algebra.FormallyEtale (MvPolynomial (Fin n) (MvPolynomial (Fin e) K))
        (MvPolynomial (Fin e) K ⊗[K] Γ(T, c.U)) := formallyEtale_tensorCoordinates
    exact RingHom.formallyEtale_algebraMap.mpr h
  -- (ii) the base change K[u] ⊗ Γ(U) → B ⊗ Γ(U) of K[u] → B
  let M : MvPolynomial (Fin e) K ⊗[K] Γ(T, c.U) →ₐ[K] B ⊗[K] Γ(T, c.U) :=
    Algebra.TensorProduct.map φ (AlgHom.id K Γ(T, c.U))
  have h2 : M.toRingHom.FormallyEtale := by
    let R' := MvPolynomial (Fin e) K ⊗[K] Γ(T, c.U)
    let _ : Algebra R' (B ⊗[K] Γ(T, c.U)) := M.toRingHom.toAlgebra
    let _ : Algebra Γ(T, c.U) (B ⊗[K] Γ(T, c.U)) := Algebra.TensorProduct.rightAlgebra
    let _ : Algebra Γ(T, c.U) R' := Algebra.TensorProduct.rightAlgebra
    have : IsScalarTower (MvPolynomial (Fin e) K) R' (B ⊗[K] Γ(T, c.U)) :=
      IsScalarTower.of_algebraMap_eq fun s => by
        change (φ s) ⊗ₜ[K] (1 : Γ(T, c.U)) = M (s ⊗ₜ 1)
        simp [M]
    have : IsScalarTower K R' (B ⊗[K] Γ(T, c.U)) :=
      IsScalarTower.of_algebraMap_eq fun k => (M.commutes k).symm
    have : IsScalarTower Γ(T, c.U) R' (B ⊗[K] Γ(T, c.U)) :=
      IsScalarTower.of_algebraMap_eq fun g => by
        change (1 : B) ⊗ₜ[K] g = M (1 ⊗ₜ g)
        simp [M]
    have : IsScalarTower K Γ(T, c.U) (B ⊗[K] Γ(T, c.U)) :=
      IsScalarTower.of_algebraMap_eq fun k => by
        change algebraMap K _ k = (1 : B) ⊗ₜ[K] algebraMap K Γ(T, c.U) k
        rw [Algebra.TensorProduct.algebraMap_apply, ← mul_one (algebraMap K B k),
          ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    have hpo : Algebra.IsPushout (MvPolynomial (Fin e) K) B R' (B ⊗[K] Γ(T, c.U)) :=
      (Algebra.IsPushout.comp_iff K (MvPolynomial (Fin e) K) Γ(T, c.U) (T := B) (S' := R')
        (T' := B ⊗[K] Γ(T, c.U))).mp inferInstance
    have hpo' : Algebra.IsPushout (MvPolynomial (Fin e) K) R' B (B ⊗[K] Γ(T, c.U)) := hpo.symm
    have hbc : Algebra.FormallyEtale R' (R' ⊗[MvPolynomial (Fin e) K] B) := inferInstance
    have hfe : Algebra.FormallyEtale R' (B ⊗[K] Γ(T, c.U)) :=
      Algebra.FormallyEtale.of_equiv (R := R') (A := R' ⊗[MvPolynomial (Fin e) K] B)
        (Algebra.IsPushout.equiv (MvPolynomial (Fin e) K) R' B (B ⊗[K] Γ(T, c.U)))
    exact RingHom.formallyEtale_algebraMap.mpr hfe
  -- the factorization of the coordinates
  let comp : MvPolynomial (Fin (n + e)) K →ₐ[K]
      Γ(specFibreProduct K B T, specFibreProductSnd K B T ⁻¹ᵁ c.U) :=
    ((specFibreProductSectionsEquiv c.isAffine).toAlgHom.restrictScalars K).comp
      (M.comp ((Tc.restrictScalars K).comp (productVariablesEquiv K n e).toAlgHom))
  have hcomp : fibreProductCoords c φ = comp := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · rw [fibreProductCoords_X_castAdd]
      change _ = specFibreProductSectionsEquiv c.isAffine
        (M (Tc (productVariablesEquiv K n e (MvPolynomial.X (Fin.castAdd e j)))))
      rw [productVariablesEquiv_X_castAdd, tensorCoordinates_X]
      simp only [M, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]
      rfl
    · rw [fibreProductCoords_X_natAdd]
      change _ = specFibreProductSectionsEquiv c.isAffine
        (M (Tc (productVariablesEquiv K n e (MvPolynomial.X (Fin.natAdd n l)))))
      rw [productVariablesEquiv_X_natAdd, tensorCoordinates_C]
      simp only [M, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  have hfac : (fibreProductCoords c φ).toRingHom =
      (specFibreProductSectionsEquiv c.isAffine).toRingEquiv.toRingHom.comp
        (M.toRingHom.comp (Tc.toRingHom.comp
          (productVariablesEquiv K n e).toRingEquiv.toRingHom)) := by
    rw [hcomp]
    rfl
  rw [hfac]
  refine RingHom.FormallyEtale.comp ?_ (ringHom_formallyEtale_of_etale _
    (RingHom.Etale.of_bijective (specFibreProductSectionsEquiv c.isAffine).bijective))
  refine RingHom.FormallyEtale.comp ?_ h2
  exact RingHom.FormallyEtale.comp (ringHom_formallyEtale_of_etale _
    (RingHom.Etale.of_bijective (productVariablesEquiv K n e).bijective)) h1

/-- The structure morphism of the spectrum of a nonzero K-algebra is surjective. -/
theorem specMap_algebraMap_surjective [Nontrivial B] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
  constructor
  intro x
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum B) := inferInstance
  refine ⟨y, ?_⟩
  have : Subsingleton (PrimeSpectrum K) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum K) _ _

/-- **The étale chart of the fibre product** Spec B ×_K T over the inverse image of an étale chart
c of T, with the coordinates of c and the formally étale coordinates of B. -/
noncomputable def fibreProductEtaleChart [Nontrivial B] (c : EtaleChart K T n)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale) :
    EtaleChart K (specFibreProduct K B T) (n + e) where
  U := specFibreProductSnd K B T ⁻¹ᵁ c.U
  isAffine := by
    have : IsAffineHom (specFibreProductSnd K B T) := MorphismProperty.pullback_snd _ _ inferInstance
    exact c.isAffine.preimage _
  nonempty := by
    obtain ⟨⟨t, ht⟩⟩ := c.nonempty
    have : Surjective (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) :=
      specMap_algebraMap_surjective
    obtain ⟨p, hp⟩ := (specFibreProductSnd K B T).surjective t
    exact ⟨⟨p, show specFibreProductSnd K B T p ∈ c.U from hp ▸ ht⟩⟩
  coords := fibreProductCoords c φ
  formallyEtale := fibreProductCoords_formallyEtale c φ hφ

end ChartConstruction

end MixedFujita
