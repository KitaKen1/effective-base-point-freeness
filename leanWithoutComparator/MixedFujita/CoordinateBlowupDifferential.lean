/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupRelativeCanonical

/-! A center involving only a subset of the coordinates contributes one
exceptional factor per non-pivot normal coordinate. Tangential coordinates
contribute determinant one. -/

@[expose] public section
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {A : Type*} [CommRing A] {n : ℕ}

noncomputable def coordinateBlowupDifferentialMatrix (z : Fin n → A)
    (s : Finset (Fin n)) (k : Fin n) : Matrix (Fin n) (Fin n) A :=
  fun i j => (if j ∈ s.erase k then z k else 1) *
    (Matrix.updateCol 1 k (fun i => if i = k then 1 else if i ∈ s then z i else 0)) i j

theorem coordinateBlowupDifferentialMatrix_det (z : Fin n → A)
    (s : Finset (Fin n)) (k : Fin n) :
    (coordinateBlowupDifferentialMatrix z s k).det = z k ^ (s.erase k).card := by
  classical
  let v := fun i => if i = k then (1 : A) else if i ∈ s then z i else 0
  have hv : (fun j => ∑ i, v i • (1 : Matrix (Fin n) (Fin n) A) j i) = v := by
    funext j
    simp [Matrix.one_apply, smul_eq_mul]
  have hdet : (Matrix.updateCol (1 : Matrix (Fin n) (Fin n) A) k v).det = 1 := by
    rw [← hv, Matrix.det_updateCol_sum, Matrix.det_one]
    simp [v]
  change (Matrix.of (fun i j => (if j ∈ s.erase k then z k else 1) *
    (Matrix.updateCol 1 k v) i j)).det = _
  rw [Matrix.det_mul_row, hdet, mul_one]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

theorem coordinateBlowup_kaehler_determinant {K : Type*} [Field K] [Algebra K A]
    (z x : Fin n → A) (s : Finset (Fin n)) (k : Fin n)
    (hx : ∀ i, x i = if i = k then z k else if i ∈ s then z i * z k else z i)
    (b : Module.Basis (Fin n) A Ω[A⁄K])
    (hb : ∀ i, b i = KaehlerDifferential.D K A (z i)) :
    b.det (fun i => KaehlerDifferential.D K A (x i)) = z k ^ (s.erase k).card := by
  classical
  have hm : b.toMatrix (fun i => KaehlerDifferential.D K A (x i)) =
      (coordinateBlowupDifferentialMatrix z s k).transpose := by
    ext j i
    rw [Module.Basis.toMatrix_apply, hx]
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j
        simp [← hb, coordinateBlowupDifferentialMatrix]
      · simp [← hb, coordinateBlowupDifferentialMatrix, Matrix.transpose_apply,
          hj, Ne.symm hj]
    · by_cases his : i ∈ s
      · rw [ite_eq_right hi, ite_eq_left his, Derivation.leibniz, map_add, map_smul, map_smul,
          ← hb i, ← hb k]
        simp [coordinateBlowupDifferentialMatrix, Matrix.transpose_apply,
          Matrix.updateCol_apply, Matrix.one_apply, hi, his, smul_eq_mul]
        split_ifs <;> simp_all
      · by_cases hj : j = i
        · subst j
          simp [hi, his, ← hb, coordinateBlowupDifferentialMatrix]
        · simp [hi, his, ← hb, coordinateBlowupDifferentialMatrix, Matrix.transpose_apply,
            Matrix.updateCol_apply, hj, Ne.symm hj]
  rw [Module.Basis.det_apply, hm, Matrix.det_transpose, coordinateBlowupDifferentialMatrix_det]

theorem coordinateBlowup_etaleRelativeJacobian_det
    {K R S : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    (β : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
    (s : Finset (Fin n)) (k : Fin n)
    (hcoord : ∀ i, β (x (MvPolynomial.X i)) = if i = k then y (MvPolynomial.X k)
      else if i ∈ s then y (MvPolynomial.X i) * y (MvPolynomial.X k)
      else y (MvPolynomial.X i)) :
    (etaleRelativeJacobian β x y hy).det = y (MvPolynomial.X k) ^ (s.erase k).card := by
  rw [etaleRelativeJacobian_det]
  exact coordinateBlowup_kaehler_determinant _ _ s k hcoord (etaleCoordinateBasis y hy)
    (etaleCoordinateBasis_apply y hy)

end MixedFujita
