/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateHyperplaneJacobian
public import MixedFujita.RelativeCanonicalDivisor

/-!
The residue of the relative Jacobian along a coordinate hyperplane in a target algebra
(step 15, adjunction for the klt restriction theorem).

For a K-algebra map ψ : R → S, coordinates x of R (any map) and étale coordinates y of S with
ψ(x_0) = y_0 w, and a K-algebra map g : S → F killing y_0 such that g(y_1), …, g(y_N) are étale
coordinates of F, the residue of the Jacobian is g(det J(ψ)) = g(w) · det J', where J' is the
Jacobian of the functions g(ψ(x_1)), …, g(ψ(x_N)) of F in these coordinates
(`etaleRelativeJacobian_det_residue`). This is `etaleRelativeJacobian_det_quotient` transported
to F along the map S/(y_0) → F induced by g. Permuting the source coordinates permutes the rows
(`etaleRelativeJacobian_det_rename`). In the adjunction, S is the stalk of the model at the
generic point of the strict transform of the hyperplane, F the function field of the strict
transform, and x the coordinates of a chart of the singular variety at the generic point of the
hyperplane, which need not be regular at any point of the strict transform over the singular
point.
-/

@[expose] public section

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

section Residue

variable {K R S F : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
  [CommRing F] [Algebra K F]

/-- The relative Jacobian only depends on the functions ψ(x_i). -/
theorem etaleRelativeJacobian_eq_of_apply_eq {n : ℕ} {R' : Type*} [CommRing R'] [Algebra K R']
    (ψ : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R) (ψ' : R' →ₐ[K] S)
    (x' : MvPolynomial (Fin n) K →ₐ[K] R') (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale)
    (h : ∀ i, ψ (x (MvPolynomial.X i)) = ψ' (x' (MvPolynomial.X i))) :
    etaleRelativeJacobian ψ x y hy = etaleRelativeJacobian ψ' x' y hy := by
  ext i j
  simp only [etaleRelativeJacobian, Matrix.of_apply, h i]

/-- Renaming the source coordinates by a permutation permutes the rows of the relative
Jacobian. -/
theorem etaleRelativeJacobian_det_rename {n : ℕ} (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (π : Equiv.Perm (Fin n)) :
    (etaleRelativeJacobian ψ (x.comp (MvPolynomial.rename π)) y hy).det =
      Equiv.Perm.sign π * (etaleRelativeJacobian ψ x y hy).det := by
  have h : etaleRelativeJacobian ψ (x.comp (MvPolynomial.rename π)) y hy =
      (etaleRelativeJacobian ψ x y hy).submatrix π id := by
    ext i j
    simp only [etaleRelativeJacobian, Matrix.of_apply, Matrix.submatrix_apply, id_eq,
      AlgHom.comp_apply, MvPolynomial.rename_X]
  rw [h, Matrix.det_permute]

variable {N : ℕ}

/-- **The residue of the relative Jacobian along y_0 = 0 in a target algebra**: if ψ(x_0) = y_0 w
and g kills y_0 with g(y_1), …, g(y_N) étale coordinates yF of F, then
g(det J(ψ)) = g(w) · det J', with J' the Jacobian in the coordinates yF of the functions
xF_k = g(ψ(x_{k+1})). -/
theorem etaleRelativeJacobian_det_residue (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin (N + 1)) K →ₐ[K] R) (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (w : S)
    (hw : ψ (x (MvPolynomial.X 0)) = y (MvPolynomial.X 0) * w)
    (g : S →ₐ[K] F) (hg0 : g (y (MvPolynomial.X 0)) = 0)
    (yF : MvPolynomial (Fin N) K →ₐ[K] F)
    (hyF : ∀ k, yF (MvPolynomial.X k) = g (y (MvPolynomial.X k.succ)))
    (hyFe : yF.toRingHom.FormallyEtale) (xF : MvPolynomial (Fin N) K →ₐ[K] F)
    (hxF : ∀ k, xF (MvPolynomial.X k) = g (ψ (x (MvPolynomial.X k.succ)))) :
    g (etaleRelativeJacobian ψ x y hy).det =
      g w * (etaleRelativeJacobian (AlgHom.id K F) xF yF hyFe).det := by
  let I : Ideal S := Ideal.span {y (MvPolynomial.X 0)}
  have h : Ideal.span {x (MvPolynomial.X 0)} ≤ I.comap ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change ψ (x (MvPolynomial.X 0)) ∈ I
    rw [hw]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hq := etaleRelativeJacobian_det_quotient ψ x y hy w hw h
  -- the map S/(y_0) → F induced by g
  have hgI : ∀ a : S, a ∈ I → g a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hg0, mul_zero]
  let gb : (S ⧸ I) →ₐ[K] F := Ideal.Quotient.liftₐ I g hgI
  have hgb : ∀ a : S, gb (Ideal.Quotient.mk I a) = g a := fun a => rfl
  have hcoords : gb.comp (hyperplaneCoords y) = yF := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [AlgHom.comp_apply, hyperplaneCoords_X, hgb, hyF]
  have hgbe : (gb.comp (hyperplaneCoords y)).toRingHom.FormallyEtale := by
    rw [hcoords]
    exact hyFe
  have h1 := congrArg gb hq
  rw [map_mul, hgb, hgb] at h1
  rw [h1]
  congr 1
  rw [← etaleRelativeJacobian_det_comp_coords (Ideal.quotientMapₐ I ψ h) gb (hyperplaneCoords x)
    (hyperplaneCoords y) (hyperplaneCoords_formallyEtale y hy) hgbe]
  rw [etaleRelativeJacobian_congr (gb.comp (Ideal.quotientMapₐ I ψ h)) rfl hcoords hgbe hyFe]
  congr 1
  apply etaleRelativeJacobian_eq_of_apply_eq
  intro k
  rw [AlgHom.comp_apply, hyperplaneCoords_X, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
    hgb, AlgHom.id_apply, hxF]

end Residue

end MixedFujita
