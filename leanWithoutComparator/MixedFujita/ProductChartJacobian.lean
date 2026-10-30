/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreProductEtaleChart

/-!
Jacobian determinants of product charts (step 15).

Two bases of a module over S indexed by Fin (n + e) that agree on the last e vectors and whose
first n vectors are the images of two bases b, b' of a module over R under a σ-semilinear map have
the determinant σ(det(b, b')): the change of basis matrix is block diagonal with blocks the image
of the change of basis matrix of b, b' and the identity (`basis_det_append_eq_map`). For the
Kähler differentials of a K-algebra map σ : R → S this is the statement that the Jacobian
determinant of two coordinate systems (z, u) and (z', u) with the same last coordinates is the
image of the Jacobian determinant of z and z' (`kaehler_basis_det_append_eq_map`), the algebra
behind the canonical equations of the charts of a fibre product.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

/-- The two embeddings of Fin n and Fin e into Fin (n + e) have disjoint images. -/
theorem castAdd_ne_natAdd_fin {n e : ℕ} (j : Fin n) (l : Fin e) :
    Fin.castAdd e j ≠ Fin.natAdd n l := by
  intro h
  have h1 := congrArg Fin.val h
  have h2 := j.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h1
  omega

section Linear

variable {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) {N M : Type*} [AddCommGroup N]
  [Module R N] [AddCommGroup M] [Module S M] {n e : ℕ}

/-- The coordinates in B of the image of a vector of the first block. -/
theorem basis_repr_image_castAdd (F : N →+ M) (hF : ∀ (r : R) (x : N), F (r • x) = σ r • F x)
    (b : Module.Basis (Fin n) R N) (B : Module.Basis (Fin (n + e)) S M)
    (hB : ∀ j, B (Fin.castAdd e j) = F (b j)) (x : N) (i : Fin (n + e)) :
    B.repr (F x) i =
      Fin.addCases (fun j => σ (b.repr x j)) (fun _ => (0 : S)) i := by
  classical
  have hx : F x = ∑ j, σ (b.repr x j) • B (Fin.castAdd e j) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, hB]
  rw [hx, map_sum, Finsupp.finsetSum_apply]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  refine Fin.addCases (fun j => ?_) (fun l => ?_) i
  · simp only [Fin.addCases_left]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      exact ite_eq_right_iff.mpr fun h => absurd (Fin.castAdd_injective _ _ h) hj'
    · intro h
      exact absurd (Finset.mem_univ j) h
  · simp only [Fin.addCases_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact ite_eq_right_iff.mpr fun h => absurd h (castAdd_ne_natAdd_fin j l)

/-- **Block Jacobians**: two bases of M indexed by Fin (n + e) which agree on the last e vectors
and whose first n vectors are the images under a σ-semilinear map of two bases b, b' of N have the
determinant σ(det(b, b')). -/
theorem basis_det_append_eq_map (F : N →+ M) (hF : ∀ (r : R) (x : N), F (r • x) = σ r • F x)
    (b b' : Module.Basis (Fin n) R N) (B B' : Module.Basis (Fin (n + e)) S M)
    (hB : ∀ j, B (Fin.castAdd e j) = F (b j)) (hB' : ∀ j, B' (Fin.castAdd e j) = F (b' j))
    (hBB' : ∀ l, B' (Fin.natAdd n l) = B (Fin.natAdd n l)) :
    B.det B' = σ (b.det b') := by
  classical
  have hmat : B.toMatrix B' = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks ((b.toMatrix b').map σ) 0 0 1) := by
    ext i k
    rw [Module.Basis.toMatrix_apply]
    refine Fin.addCases (fun j' => ?_) (fun l' => ?_) k
    · rw [hB', basis_repr_image_castAdd σ F hF b B hB]
      refine Fin.addCases (fun j => ?_) (fun l => ?_) i
      · simp [Matrix.reindex_apply, Module.Basis.toMatrix_apply]
      · simp [Matrix.reindex_apply]
    · rw [hBB', Module.Basis.repr_self]
      refine Fin.addCases (fun j => ?_) (fun l => ?_) i
      · simp [Matrix.reindex_apply, (castAdd_ne_natAdd_fin j l').symm]
      · simp [Matrix.reindex_apply, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  rw [Module.Basis.det_apply, hmat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Module.Basis.det_apply]

end Linear

section ProductCharts

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra structureSectionsAlgebra
  specFibreProductOverAlgebra specFibreProductOverField specFibreProduct_isScalarTower
  functionFieldBaseAlgebra

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {T : Scheme.{u}}
  [T.Over (Spec (CommRingCat.of K))] {n e : ℕ}

/-- The germ in the function field of a constant from the base ring does not depend on the open. -/
theorem germ_algebraMap_structureSections (P : Scheme.{u}) [IsIntegral P]
    [P.Over (Spec (CommRingCat.of B))] (U : P.Opens) [Nonempty U] (b : B) :
    P.germToFunctionField U (algebraMap B Γ(P, U) b) =
      P.germToFunctionField ⊤ (Scheme.Modules.baseRingToGlobalSections B P b) := by
  change P.germToFunctionField U (((P.baseRingToStructurePresheaf B).app (op U)) b) = _
  rw [Scheme.baseRingToStructurePresheaf_app]
  exact TopCat.Presheaf.germ_res_apply P.presheaf U.leTop _ _ _

/-- The second projection of the fibre product is surjective, hence dominant. -/
theorem specFibreProductSnd_isDominant [Nontrivial B] : IsDominant (specFibreProductSnd K B T) := by
  have : Surjective (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) :=
    specMap_algebraMap_surjective
  exact ⟨(specFibreProductSnd K B T).surjective.denseRange⟩

/-- The second projection of the fibre product is a morphism over K. -/
theorem specFibreProductSnd_isOver : (specFibreProductSnd K B T).IsOver (Spec (CommRingCat.of K)) :=
  ⟨pullback.condition.symm⟩

attribute [local instance] specFibreProductSnd_isDominant specFibreProductSnd_isOver

/-- **The canonical equations of product charts** of Spec B ×_K T with the same coordinates of B
are the images of the canonical equations of the charts of T under the function field map of the
second projection. -/
theorem fibreProductChart_canonicalEquation [Nontrivial B] [IsIntegral T]
    [IsIntegral (specFibreProduct K B T)] (c₀ c : EtaleChart K T n)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale) :
    (etaleChartCanonicalEquation (fibreProductEtaleChart c₀ φ hφ)
        (fibreProductEtaleChart c φ hφ) : (specFibreProduct K B T).functionField) =
      dominantFunctionFieldAlgHom (K := K) (specFibreProductSnd K B T)
        (etaleChartCanonicalEquation c₀ c : T.functionField) := by
  classical
  let σ := dominantFunctionFieldAlgHom (K := K) (specFibreProductSnd K B T)
  let _ : Algebra T.functionField (specFibreProduct K B T).functionField := σ.toRingHom.toAlgebra
  have : IsScalarTower K T.functionField (specFibreProduct K B T).functionField :=
    IsScalarTower.of_algebraMap_eq fun k => (σ.commutes k).symm
  let F := KaehlerDifferential.map K K T.functionField (specFibreProduct K B T).functionField
  have hFD : ∀ x, F (KaehlerDifferential.D K T.functionField x) =
      KaehlerDifferential.D K (specFibreProduct K B T).functionField (σ x) := fun x =>
    KaehlerDifferential.map_D K K _ _ x
  -- the first coordinates are the pulled back coordinates of T
  have hcast : ∀ (c' : EtaleChart K T n) (j : Fin n),
      etaleChartBasis (fibreProductEtaleChart c' φ hφ) (Fin.castAdd e j) =
        F (etaleChartBasis c' j) := by
    intro c' j
    unfold etaleChartBasis
    rw [etaleCoordinateBasis_apply, etaleCoordinateBasis_apply, hFD]
    congr 1
    change (specFibreProduct K B T).germToFunctionField _
      (fibreProductCoords c' φ (MvPolynomial.X (Fin.castAdd e j))) =
        σ (T.germToFunctionField c'.U (c'.coords (MvPolynomial.X j)))
    rw [fibreProductCoords_X_castAdd, specFibreProductSectionsEquiv_tmul, map_one, one_mul]
    exact (dominantFunctionFieldMap_germ (specFibreProductSnd K B T) c'.U
      (specFibreProductSnd K B T ⁻¹ᵁ c'.U) le_rfl _).symm
  -- the last coordinates are the coordinates of B
  have hnat : ∀ l : Fin e,
      etaleChartBasis (fibreProductEtaleChart c₀ φ hφ) (Fin.natAdd n l) =
        etaleChartBasis (fibreProductEtaleChart c φ hφ) (Fin.natAdd n l) := by
    intro l
    unfold etaleChartBasis
    rw [etaleCoordinateBasis_apply, etaleCoordinateBasis_apply]
    congr 1
    change (specFibreProduct K B T).germToFunctionField _
        (fibreProductCoords c₀ φ (MvPolynomial.X (Fin.natAdd n l))) =
      (specFibreProduct K B T).germToFunctionField _
        (fibreProductCoords c φ (MvPolynomial.X (Fin.natAdd n l)))
    rw [fibreProductCoords_X_natAdd, fibreProductCoords_X_natAdd,
      specFibreProductSectionsEquiv_tmul, specFibreProductSectionsEquiv_tmul]
    simp only [map_one, mul_one]
    have : Nonempty (specFibreProductSnd K B T ⁻¹ᵁ c₀.U) := (fibreProductEtaleChart c₀ φ hφ).nonempty
    have : Nonempty (specFibreProductSnd K B T ⁻¹ᵁ c.U) := (fibreProductEtaleChart c φ hφ).nonempty
    rw [germ_algebraMap_structureSections, germ_algebraMap_structureSections]
  rw [etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val]
  exact basis_det_append_eq_map σ.toRingHom F.toAddMonoidHom
    (fun r x => by simp only [LinearMap.toAddMonoidHom_coe, LinearMap.map_smul_of_tower]; rfl)
    (etaleChartBasis c) (etaleChartBasis c₀) _ _ (hcast c) (hcast c₀) hnat

end ProductCharts

end MixedFujita
