/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GenericRestriction
public import MixedFujita.TwistedCartierApproximation
public import MixedFujita.SNCBoundaryLocalProduct

/-!
The log discrepancy inequality along a prime of a test model of a fibre, for pairs on singular
varieties (step 15, generic restriction for klt pairs).

The discrepancy divisor d(K_T − σ*(K_Y + B)) = d div(σ*ω) − σ*D of a pair (c₀, f₀, d, D) along a
birational σ : T → Y has the local equation (σ*f₀ J(c₀, c'))^d / σ*h at t, for a chart c' at t
and a local equation h of D at σ(t) (`logDiscrepancyDivisor_isLocalEquationAt`); no chart of Y at
σ(t) is needed.

Let α : W → T map a smooth n-dimensional W into a smooth (n + e)-dimensional model T, ρ : T → P be
birational and π : P → Y with σ = α ≫ ρ ≫ π dominant and birational, and let the pair on P be the
pullback (c_P, π*f_Y, d, π*D₀) of a pair on Y, with discrepancy divisor of ρ supported on a simple
normal crossing family ξ. For a prime x of W and a simple normal crossing chart F at α(x) whose
members are among its first n coordinates, the orders o_s of the members along x satisfy

  d Σ_s o_s + Σ_s L_s o_s ≤ d + (coefficient at x of the discrepancy divisor of σ),

with L_s the coefficients of the discrepancy divisor of ρ (`fibre_snc_logDiscrepancy_le`), provided
the chart c_P is a product chart at the image of the generic point of W: its first n coordinates
pulled back from c_Y by π, its last e coordinates pulled back by ρ to the last e coordinates of F,
which are constant along α. Unlike check 314 (`fibre_snc_discrepancy_le`), where Y is smooth and
charts at the points are used, the Jacobian of σ is factored at the generic points, where the
charts of Y and of P are defined even when σ(x) is a singular point: in the function field of W,
J_σ(c_Y, c_W) = α*(N) det Q, with N the n × n block of the Jacobian of ρ at the generic point of
α(W) and Q the Jacobian of the pulled back fibre coordinates at x. The discrepancy divisor of ρ
has a local product at α(x), whose pullback along α has order Σ_s L_s o_s; and the order of det Q
is at least Σ_s o_s − 1 (logarithmic poles, as in check 314).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- A ring homomorphism viewed as a monoid homomorphism has the same values. -/
theorem ringHom_toMonoidHom_apply {A B : Type*} [NonAssocSemiring A] [NonAssocSemiring B]
    (φ : A →+* B) (a : A) : φ.toMonoidHom a = φ a := rfl

section LocalEquation

variable {K : Type u} [Field K] {n : ℕ} {Y T : Scheme.{u}} [IsIntegral Y] [IsIntegral T]
  [Y.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (σ : T ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- **The local equation of the discrepancy divisor of a pair** at t: for a chart c' at t and a
local equation h of D at σ(t), it is (σ*f₀ J(c₀, c'))^d / σ*h. No chart of Y at σ(t) is used. -/
theorem logDiscrepancyDivisor_isLocalEquationAt (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor Y) (c'₀ : EtaleChart K T n) (t : T) (c' : EtaleChart K T n)
    (hc' : t ∈ c'.U) {h : Y.functionFieldˣ} (hh : D.IsLocalEquationAt (σ t) h) :
    (logDiscrepancyDivisor n σ hσ c₀ f₀ d D c'₀ etaleCharts_cover).IsLocalEquationAt t
      ((Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom f₀ *
        (isUnit_chartRelativeJacobianDet_of_bijective σ hσ c₀ c').unit) ^ d *
        (Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom h)⁻¹) := by
  unfold logDiscrepancyDivisor pullbackFormDivisor
  have h1 := canonicalDivisor_isLocalEquationAt c'₀ etaleCharts_cover c' hc'
  have h2 := CartierDivisor.isLocalEquationAt_principalCartierDivisor t
    (Units.map (dominantFunctionFieldMap σ).hom.toMonoidHom f₀ *
      (isUnit_chartRelativeJacobianDet_of_bijective σ hσ c₀ c'₀).unit)
  have h3 := isLocalEquationAt_nsmul (h1.mul h2) d
  have h4 := (cartierPullback_isLocalEquationAt σ D t hh).inv
  have h5 := h3.mul h4
  rw [← sub_eq_add_neg] at h5
  convert h5 using 2
  congr 1
  apply Units.ext
  have hJ := chartRelativeJacobianDet_change σ c₀ c₀ c'₀ c'
  have hg : (etaleChartCanonicalEquation c₀ c₀ : Y.functionField) = 1 := by
    rw [etaleChartCanonicalEquation_val, Module.Basis.det_self]
  rw [hg, map_one, one_mul] at hJ
  simp only [Units.val_mul, IsUnit.unit_spec]
  rw [hJ]
  ring

end LocalEquation

section Stalks

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- At a point equal to the generic point, every rational function is the image of an element
of the stalk. -/
theorem exists_stalk_eq_of_eq_genericPoint {y : Y} (hy : y = genericPoint Y)
    (f : Y.functionField) :
    ∃ b : Y.presheaf.stalk y, stalkFunctionFieldAlgHom (K := K) y b = f := by
  obtain ⟨U, hU, s, hs⟩ := Y.presheaf.exists_germ_eq (x := genericPoint Y) f
  have hyU : y ∈ U := hy ▸ hU
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  refine ⟨Y.presheaf.germ U y hyU s, ?_⟩
  change algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ U y hyU s) = f
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact hs

/-- The images in the function field of the stalks commute with specialization. -/
theorem stalkFunctionFieldAlgHom_stalkSpecializes {x x' : Y} (h : x ⤳ x')
    (a : Y.presheaf.stalk x') :
    stalkFunctionFieldAlgHom (K := K) x (Y.presheaf.stalkSpecializes h a) =
      stalkFunctionFieldAlgHom (K := K) x' a := by
  change algebraMap (Y.presheaf.stalk x) Y.functionField (Y.presheaf.stalkSpecializes h a) =
    algebraMap (Y.presheaf.stalk x') Y.functionField a
  simp only [RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

end Stalks

section StalkGerms

variable {K : Type u} [Field K] {W T : Scheme.{u}} [IsIntegral W]
  [W.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))] (α : W ⟶ T)
  [α.IsOver (Spec (CommRingCat.of K))]

/-- The image in the function field of the pullback of a germ is the function of the pulled back
section. Stated with `stalkFunctionFieldAlgHom`, so that it also applies at the generic point. -/
theorem stalkFunctionFieldAlgHom_stalkMap_germ (w : W) (U : T.Opens) (hw : α w ∈ U)
    (s : Γ(T, U)) [Nonempty (α ⁻¹ᵁ U)] :
    stalkFunctionFieldAlgHom (K := K) w (schemeStalkMapAlgHom (K := K) α w
      (T.presheaf.germ U (α w) hw s)) = W.germToFunctionField (α ⁻¹ᵁ U) (α.app U s) := by
  change algebraMap (W.presheaf.stalk w) W.functionField
    (α.stalkMap w (T.presheaf.germ U (α w) hw s)) = _
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.algebraMap_germ_eq_germToFunctionField]

end StalkGerms

section ChainRule

variable {K : Type u} [Field K] {n e : ℕ} {W T P Y : Scheme.{u}}
  [IsIntegral W] [IsLocallyNoetherian W] [W.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (W ↘ Spec (CommRingCat.of K))]
  [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension (n + e) (T ↘ Spec (CommRingCat.of K))]
  [IsIntegral P] [P.Over (Spec (CommRingCat.of K))]
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  (α : W ⟶ T) [α.IsOver (Spec (CommRingCat.of K))]
  (ρ : T ⟶ P) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (π : P ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsDominant (α ≫ ρ ≫ π)]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π)))

set_option maxHeartbeats 1600000 in
include hρ hσ in
/-- **The log discrepancy inequality along a prime of a test model of a fibre, for a pulled back
pair on a singular variety**: if the chart c_P of P is a product chart at the image of the generic
point of W (its first n coordinates pulled back from c_Y by π, its last e pulled back by ρ to the
last e coordinates of the fibre chart F, which are constant along α), then
d Σ_s o_s + Σ_s L_s o_s ≤ d + (coefficient at x of the discrepancy divisor of α ≫ ρ ≫ π), with
L_s the coefficients of the discrepancy divisor of ρ for the pair (c_P, π*f_Y, d, π*D₀) and o_s
the orders of the member coordinates of F along x. -/
theorem fibre_snc_logDiscrepancy_le (cP : EtaleChart K P (n + e)) (cT : EtaleChart K T (n + e))
    (cY : EtaleChart K Y n) (cW : EtaleChart K W n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ : CartierDivisor Y) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K (n + e) ξ)
    (hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (logDiscrepancyDivisor (n + e) ρ hρ cP
        (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom fY) d (cartierPullback π D₀) cT
        etaleCharts_cover) (z : T) = 0)
    (x : CodimensionOnePoint W) (F : EtaleChart K T (n + e)) (hF : α (x : W) ∈ F.U)
    (σF : Fin r → Option (Fin (n + e))) (hFsnc : IsSNCChart F ξ σF)
    (hσF : ∀ k a, σF k = some a → (a : ℕ) < n)
    (hFη : α (genericPoint W) ∈ F.U) (hPη : ρ (α (genericPoint W)) ∈ cP.U)
    (hYη : (α ≫ ρ ≫ π) (genericPoint W) ∈ cY.U)
    (P1 : ∀ i : Fin n, schemeStalkMapAlgHom (K := K) (α ≫ ρ ≫ π) (genericPoint W)
        (etaleChartStalkCoords cY _ hYη (MvPolynomial.X i)) =
      schemeStalkMapAlgHom (K := K) α (genericPoint W) (schemeStalkMapAlgHom (K := K) ρ
        (α (genericPoint W)) (etaleChartStalkCoords cP _ hPη
          (MvPolynomial.X (Fin.castAdd e i)))))
    (P2 : ∀ l : Fin e, schemeStalkMapAlgHom (K := K) ρ (α (genericPoint W))
        (etaleChartStalkCoords cP _ hPη (MvPolynomial.X (Fin.natAdd n l))) =
      etaleChartStalkCoords F _ hFη (MvPolynomial.X (Fin.natAdd n l)))
    (P3 : ∀ l : Fin e, ∃ κ : K, schemeStalkMapAlgHom (K := K) α (genericPoint W)
        (etaleChartStalkCoords F _ hFη (MvPolynomial.X (Fin.natAdd n l))) = algebraMap K _ κ) :
    (d : ℤ) * ∑ s, fibreSNCOrder α (x : W) F hF σF s +
        ∑ s, cartierCoefficient (logDiscrepancyDivisor (n + e) ρ hρ cP
          (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom fY) d (cartierPullback π D₀) cT
          etaleCharts_cover) (ξ s) * fibreSNCOrder α (x : W) F hF σF s ≤
      (d : ℤ) + cartierCoefficient (logDiscrepancyDivisor n (α ≫ ρ ≫ π) hσ cY fY d D₀ cW
        etaleCharts_cover) (x : W) := by
  classical
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + e) _
  have : Smooth (W ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have : IsDiscreteValuationRing (W.presheaf.stalk (x : W)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨cW', hcW'⟩ : ∃ c : EtaleChart K W n, (x : W) ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := W) (n := n)).symm ▸
      Opens.mem_top (x : W))
  set fP : P.functionFieldˣ := Units.map (dominantFunctionFieldMap π).hom.toMonoidHom fY
    with hfP
  -- notation at the generic points
  set ψα := schemeStalkMapAlgHom (K := K) α (genericPoint W) with hψα
  set gW := stalkFunctionFieldAlgHom (K := K) (genericPoint W) with hgW
  set ψ' := gW.comp ψα with hψ'
  set ψρ := schemeStalkMapAlgHom (K := K) ρ (α (genericPoint W)) with hψρ
  set f := etaleChartStalkCoords F (α (genericPoint W)) hFη with hfdef
  have hf := etaleChartStalkCoords_formallyEtale F (α (genericPoint W)) hFη
  set p := etaleChartStalkCoords cP (ρ (α (genericPoint W))) hPη with hpdef
  set cWf := etaleChartFunctionFieldCoords cW' with hcWfdef
  have hcWf := etaleChartFunctionFieldCoords_formallyEtale cW'
  -- the n × n block of the Jacobian of ρ at the generic point of α(W)
  let Nm : Matrix (Fin n) (Fin n) (T.presheaf.stalk (α (genericPoint W))) := Matrix.of fun i i' =>
    etaleCoordinateDerivation f hf (Fin.castAdd e i') (ψρ (p (MvPolynomial.X (Fin.castAdd e i))))
  have hJρ : (etaleRelativeJacobian ψρ p f hf).det = Nm.det := by
    let B : Matrix (Fin n) (Fin e) (T.presheaf.stalk (α (genericPoint W))) := Matrix.of fun i l =>
      etaleCoordinateDerivation f hf (Fin.natAdd n l) (ψρ (p (MvPolynomial.X (Fin.castAdd e i))))
    have hblock : (etaleRelativeJacobian ψρ p f hf).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks Nm B 0 1 := by
      ext (i | l) (i' | l')
      · simp [etaleRelativeJacobian, Nm]
      · simp [etaleRelativeJacobian, B]
      · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
          etaleRelativeJacobian, Matrix.of_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        rw [P2 l, etaleCoordinateDerivation_coordinate, ite_eq_right_iff]
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_right, etaleRelativeJacobian,
          Matrix.of_apply, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
        rw [P2 l, etaleCoordinateDerivation_coordinate]
        simp only [Fin.natAdd_inj]
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hblock, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one]
  -- the Jacobian of α ≫ ρ ≫ π factors in the function field of W
  let Q' : Matrix (Fin n) (Fin n) W.functionField := Matrix.of fun i' j =>
    etaleCoordinateDerivation cWf hcWf j (ψ' (f (MvPolynomial.X (Fin.castAdd e i'))))
  have hP1' : ∀ i : Fin n, dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π)
      (etaleChartFunctionFieldCoords cY (MvPolynomial.X i)) =
        ψ' (ψρ (p (MvPolynomial.X (Fin.castAdd e i)))) := by
    intro i
    have h2 := congrArg (fun φ => φ (etaleChartStalkCoords cY _ hYη (MvPolynomial.X i)))
      (dominantFunctionFieldAlgHom_comp_stalk (K := K) (α ≫ ρ ≫ π) (genericPoint W))
    have h3 := congrArg (fun φ => φ (MvPolynomial.X i))
      (etaleChart_stalkFunctionField_comp_stalkCoords (K := K) cY _ hYη)
    simp only [AlgHom.comp_apply] at h2 h3
    rw [← h3, h2, P1 i]
    rfl
  have hJσ : chartRelativeJacobianDet (α ≫ ρ ≫ π) cY cW' = ψ' Nm.det * Q'.det := by
    have hmat : etaleRelativeJacobian (dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π))
        (etaleChartFunctionFieldCoords cY) cWf hcWf = (ψ' : _ →+* _).mapMatrix Nm * Q' := by
      ext i j
      simp only [etaleRelativeJacobian, Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, Nm, Q']
      rw [hP1' i, etaleCoordinateDerivation_chainRule_of_dims ψ' f hf cWf hcWf j,
        Fin.sum_univ_add]
      have hzero : ∀ l : Fin e, ψ' (etaleCoordinateDerivation f hf (Fin.natAdd n l)
          (ψρ (p (MvPolynomial.X (Fin.castAdd e i))))) * etaleCoordinateDerivation cWf hcWf j
            (ψ' (f (MvPolynomial.X (Fin.natAdd n l)))) = 0 := by
        intro l
        obtain ⟨κ, hκ⟩ := P3 l
        have hc : ψ' (f (MvPolynomial.X (Fin.natAdd n l))) = algebraMap K _ κ := by
          change gW (ψα (f (MvPolynomial.X (Fin.natAdd n l)))) = _
          rw [hκ, AlgHom.commutes]
        rw [hc, Derivation.map_algebraMap, mul_zero]
      simp only [hzero, Finset.sum_const_zero, add_zero]
      rfl
    unfold chartRelativeJacobianDet
    rw [hmat, Matrix.det_mul, ← RingHom.map_det]
    rfl
  -- the Jacobian of the pulled back fibre coordinates at x
  set ψe := schemeStalkMapAlgHom (K := K) α (x : W) with hψe
  set fe := etaleChartStalkCoords F (α (x : W)) hF with hfedef
  set ce := etaleChartStalkCoords cW' (x : W) hcW' with hcedef
  have hce := etaleChartStalkCoords_formallyEtale cW' (x : W) hcW'
  set σx := stalkFunctionFieldAlgHom (K := K) (x : W) with hσx
  let Q : Matrix (Fin n) (Fin n) (W.presheaf.stalk (x : W)) := Matrix.of fun i' j =>
    etaleCoordinateDerivation ce hce j (ψe (fe (MvPolynomial.X (Fin.castAdd e i'))))
  have hcoordη : ∀ a, ψ' (f (MvPolynomial.X a)) = σx (ψe (fe (MvPolynomial.X a))) := by
    intro a
    have : Nonempty (α ⁻¹ᵁ F.U) := ⟨⟨(x : W), hF⟩⟩
    have e1 : ψ' (f (MvPolynomial.X a)) = stalkFunctionFieldAlgHom (K := K) (genericPoint W)
        (schemeStalkMapAlgHom (K := K) α (genericPoint W)
          (T.presheaf.germ F.U (α (genericPoint W)) hFη (F.coords (MvPolynomial.X a)))) := rfl
    have e2 : σx (ψe (fe (MvPolynomial.X a))) = stalkFunctionFieldAlgHom (K := K) (x : W)
        (schemeStalkMapAlgHom (K := K) α (x : W)
          (T.presheaf.germ F.U (α (x : W)) hF (F.coords (MvPolynomial.X a)))) := rfl
    rw [e1, e2, stalkFunctionFieldAlgHom_stalkMap_germ, stalkFunctionFieldAlgHom_stalkMap_germ]
  have hσce : σx.comp ce = cWf := etaleChart_stalkFunctionField_comp_stalkCoords (K := K) cW' _ hcW'
  have hσy : (σx.comp ce).toRingHom.FormallyEtale := hσce ▸ hcWf
  have hQ' : Q'.det = σx Q.det := by
    have hdet := etaleRelativeJacobian_det_comp_coords ψe σx
      (fe.comp (MvPolynomial.rename (Fin.castAdd e))) ce hce hσy
    have hQe : etaleRelativeJacobian ψe (fe.comp (MvPolynomial.rename (Fin.castAdd e))) ce hce =
        Q := by
      ext i' j
      simp [etaleRelativeJacobian, Q, MvPolynomial.rename_X]
    have hQ'e : etaleRelativeJacobian (σx.comp ψe) (fe.comp (MvPolynomial.rename (Fin.castAdd e)))
        (σx.comp ce) hσy = Q' := by
      rw [etaleRelativeJacobian_congr (σx.comp ψe) rfl hσce hσy hcWf]
      ext i' j
      simp only [etaleRelativeJacobian, Q', Matrix.of_apply, AlgHom.comp_apply,
        MvPolynomial.rename_X]
      rw [hcoordη]
    rw [← hQ'e, hdet, hQe]
  -- the Jacobian of α ≫ ρ ≫ π is a unit, so the factors are nonzero
  have hRσ := isUnit_chartRelativeJacobianDet_of_bijective (α ≫ ρ ≫ π) hσ cY cW'
  have hprod0 : ψ' Nm.det * σx Q.det ≠ 0 := by
    rw [← hQ', ← hJσ]
    exact hRσ.ne_zero
  have hN0 : ψ' Nm.det ≠ 0 := left_ne_zero_of_mul hprod0
  have hQ0 : Q.det ≠ 0 := fun h0 => right_ne_zero_of_mul hprod0 (by rw [h0, map_zero])
  have hrow : ∀ i', ψe (fe (MvPolynomial.X (Fin.castAdd e i'))) ≠ 0 := by
    intro i' h0
    apply hQ0
    apply Matrix.det_eq_zero_of_row_eq_zero i'
    intro j
    simp only [Q, Matrix.of_apply, h0, map_zero]
  -- local equations of the two discrepancy divisors
  obtain ⟨h₀, hh₀⟩ := D₀.exists_isLocalEquationAt ((α ≫ ρ ≫ π) (x : W))
  have hlocσ := logDiscrepancyDivisor_isLocalEquationAt (α ≫ ρ ≫ π) hσ cY fY d D₀ cW (x : W)
    cW' hcW' hh₀
  have hh₀' : D₀.IsLocalEquationAt (π (ρ (α (x : W)))) h₀ := hh₀
  have hhP := cartierPullback_isLocalEquationAt π D₀ (ρ (α (x : W))) hh₀'
  have hlocρ := logDiscrepancyDivisor_isLocalEquationAt ρ hρ cP fP d (cartierPullback π D₀) cT
    (α (x : W)) F hF hhP
  -- the pulled back form and divisor equation, through the generic points
  have hgen : π (ρ (α (genericPoint W))) = genericPoint Y :=
    dominant_map_genericPoint (α ≫ ρ ≫ π)
  obtain ⟨bY, hbY⟩ := exists_stalk_eq_of_eq_genericPoint (K := K) hgen
    ((fY ^ d * h₀⁻¹ : Y.functionFieldˣ) : Y.functionField)
  set ψπ := schemeStalkMapAlgHom (K := K) π (ρ (α (genericPoint W))) with hψπ
  set b := ψρ (ψπ bY) with hbdef
  set gT := stalkFunctionFieldAlgHom (K := K) (α (genericPoint W)) with hgT
  have hbT : gT b = dominantFunctionFieldAlgHom (K := K) ρ (dominantFunctionFieldAlgHom (K := K) π
      ((fY ^ d * h₀⁻¹ : Y.functionFieldˣ) : Y.functionField)) := by
    rw [← hbY]
    have h1 := congrArg (fun φ => φ bY)
      (dominantFunctionFieldAlgHom_comp_stalk (K := K) π (ρ (α (genericPoint W))))
    have h2 := congrArg (fun φ => φ (ψπ bY))
      (dominantFunctionFieldAlgHom_comp_stalk (K := K) ρ (α (genericPoint W)))
    simp only [AlgHom.comp_apply] at h1 h2
    rw [h1, h2]
  have hcompY : ∀ z : Y.presheaf.stalk ((α ≫ ρ ≫ π) (genericPoint W)),
      schemeStalkMapAlgHom (K := K) (α ≫ ρ ≫ π) (genericPoint W) z = ψα (ψρ (ψπ z)) := by
    intro z
    rw [schemeStalkMapAlgHom_apply, Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]
    rfl
  have hbW : ψ' b = dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π)
      ((fY ^ d * h₀⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    have h1 := congrArg (fun φ => φ bY)
      (dominantFunctionFieldAlgHom_comp_stalk (K := K) (α ≫ ρ ≫ π) (genericPoint W))
    simp only [AlgHom.comp_apply] at h1
    rw [hcompY] at h1
    rw [← hbY]
    exact h1.symm
  -- the two local equations through the stalk element lam = b N^d at the generic point of α(W)
  obtain ⟨lam, hlam⟩ : ∃ l, l = b * Nm.det ^ d := ⟨_, rfl⟩
  have hJρ' : chartRelativeJacobianDet ρ cP F = gT Nm.det := by
    rw [chartRelativeJacobianDet_eq_stalk ρ (α (genericPoint W)) cP hPη F hFη, hJρ]
  have hlamT : gT lam = (((Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom fP *
      (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ cP F).unit) ^ d *
      (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
        (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom h₀))⁻¹ : T.functionFieldˣ) :
        T.functionField) := by
    have e1 : gT lam = dominantFunctionFieldAlgHom (K := K) ρ (dominantFunctionFieldAlgHom (K := K) π
        ((fY ^ d * h₀⁻¹ : Y.functionFieldˣ) : Y.functionField)) *
          (chartRelativeJacobianDet ρ cP F) ^ d := by
      rw [hlam, map_mul, map_pow, hbT, hJρ']
    rw [e1]
    have hcoeρ : ∀ a, dominantFunctionFieldAlgHom (K := K) ρ a =
        (dominantFunctionFieldMap ρ).hom a := fun a => rfl
    have hcoeπ : ∀ a, dominantFunctionFieldAlgHom (K := K) π a =
        (dominantFunctionFieldMap π).hom a := fun a => rfl
    rw [hcoeρ, hcoeπ]
    simp only [hfP, Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec,
      Units.val_inv_eq_inv_val, ringHom_toMonoidHom_apply, map_mul,
      map_pow, map_inv₀]
    ring
  have hlamW : (((Units.map (dominantFunctionFieldMap (α ≫ ρ ≫ π)).hom.toMonoidHom fY *
      (isUnit_chartRelativeJacobianDet_of_bijective (α ≫ ρ ≫ π) hσ cY cW').unit) ^ d *
      (Units.map (dominantFunctionFieldMap (α ≫ ρ ≫ π)).hom.toMonoidHom h₀)⁻¹ :
        W.functionFieldˣ) : W.functionField) = ψ' lam * (σx Q.det) ^ d := by
    have e1 : ψ' lam = dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π)
        ((fY ^ d * h₀⁻¹ : Y.functionFieldˣ) : Y.functionField) * (ψ' Nm.det) ^ d := by
      rw [hlam, map_mul, map_pow, hbW]
    rw [e1]
    have hcoeσ : ∀ a, dominantFunctionFieldAlgHom (K := K) (α ≫ ρ ≫ π) a =
        (dominantFunctionFieldMap (α ≫ ρ ≫ π)).hom a := fun a => rfl
    rw [hcoeσ]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec,
      Units.val_inv_eq_inv_val, ringHom_toMonoidHom_apply, map_mul,
      map_pow, map_inv₀]
    rw [hJσ, hQ']
    ring
  -- the local product of the discrepancy divisor of ρ at α(x)
  set L : Fin r → ℤ := fun s => cartierCoefficient (logDiscrepancyDivisor (n + e) ρ hρ cP fP d
    (cartierPullback π D₀) cT etaleCharts_cover) (ξ s) with hLdef
  obtain ⟨f', hf', u, hu⟩ := normal_isSNCChart_boundary_local_product hnorm
    (logDiscrepancyDivisor (n + e) ρ hρ cP fP d (cartierPullback π D₀) cT etaleCharts_cover)
    F ξ hinj hξ σF hFsnc hsupp (α (x : W)) hF
  obtain ⟨u', hu'⟩ := hlocρ.exists_unit_mul_eq hf'
  set gTx := stalkFunctionFieldAlgHom (K := K) (α (x : W)) with hgTx
  let z : Fin r → T.presheaf.stalk (α (x : W)) := fun s =>
    (σF s).elim 1 fun a => fe (MvPolynomial.X a)
  have hzval : ∀ s, (sncChartComponentEquation F σF s : T.functionField) = gTx (z s) := by
    intro s
    cases hs : σF s with
    | none => simp [sncChartComponentEquation, z, hs]
    | some a =>
      simp only [sncChartComponentEquation, z, hs, Option.elim_some,
        etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
      rw [← T.algebraMap_germ_eq_germToFunctionField hF]
      rfl
  set M : Fin r → ℕ := fun s => (L s).toNat with hMdef
  set N : Fin r → ℕ := fun s => (-L s).toNat with hNdef
  have hLMN : ∀ s, L s = (M s : ℤ) - N s := fun s => (Int.toNat_sub_toNat_neg (L s)).symm
  set cU : Fin r → T.functionFieldˣ := fun s => sncChartComponentEquation F σF s with hcU
  have hunitsT : (∏ s, cU s ^ L s) * (∏ s, cU s ^ (N s : ℤ)) = ∏ s, cU s ^ (M s : ℤ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [← zpow_add]
    congr 1
    rw [hLMN s]
    ring
  have hprodT : ∀ k : Fin r → ℕ, ∏ s, (gTx (z s)) ^ (k s) =
      ((∏ s, cU s ^ (k s : ℤ) : T.functionFieldˣ) : T.functionField) := by
    intro k
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hcU, hzval]
  have hT : gT lam * ∏ s, (gTx (z s)) ^ (N s) =
      gTx ((u' : T.presheaf.stalk (α (x : W))) * u) * ∏ s, (gTx (z s)) ^ (M s) := by
    have h1 : gT lam = gTx u' * (gTx u * ((∏ s, cU s ^ L s : T.functionFieldˣ) :
        T.functionField)) := by
      rw [hlamT, ← hu', hu]
      rfl
    rw [h1, hprodT N, hprodT M, map_mul, ← hunitsT, Units.val_mul]
    ring
  -- transfer to the stalk at the generic point of α(W), then along α
  have hspecW : genericPoint W ⤳ (x : W) := (genericPoint_spec W).specializes (Set.mem_univ _)
  have hspecT : α (genericPoint W) ⤳ α (x : W) := hspecW.map α.continuous
  set sp := T.presheaf.stalkSpecializes hspecT with hsp
  have hgsp : ∀ a, gT (sp a) = gTx a := fun a =>
    stalkFunctionFieldAlgHom_stalkSpecializes (K := K) hspecT a
  have hψsp : ∀ a, ψ' (sp a) = σx (ψe a) := by
    intro a
    have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply α (genericPoint W) (x : W) hspecW a
    have h2 : ψ' (sp a) = gW (α.stalkMap (genericPoint W) (T.presheaf.stalkSpecializes hspecT a)) :=
      rfl
    rw [h2, h1]
    exact stalkFunctionFieldAlgHom_stalkSpecializes (K := K) hspecW _
  have hinjT := IsFractionRing.injective (T.presheaf.stalk (α (genericPoint W))) T.functionField
  have hstalk : lam * ∏ s, (sp (z s)) ^ (N s) =
      sp ((u' : T.presheaf.stalk (α (x : W))) * u) * ∏ s, (sp (z s)) ^ (M s) := by
    apply hinjT
    change gT _ = gT _
    simp only [map_mul, map_prod, map_pow, hgsp]
    simpa only [map_mul] using hT
  have hW' : ψ' lam * ∏ s, (σx (ψe (z s))) ^ (N s) =
      σx (ψe ((u' : T.presheaf.stalk (α (x : W))) * u)) * ∏ s, (σx (ψe (z s))) ^ (M s) := by
    have h := congrArg ψ' hstalk
    simp only [map_mul, map_prod, map_pow, hψsp] at h
    simpa only [map_mul] using h
  -- orders along x
  have hzne : ∀ s, σx (ψe (z s)) ≠ 0 := by
    intro s
    cases hs : σF s with
    | none => simp [z, hs]
    | some a =>
      have ha := hσF s a hs
      have h0 := hrow ⟨a, ha⟩
      have heq : Fin.castAdd e (⟨a, ha⟩ : Fin n) = a := Fin.ext rfl
      rw [heq] at h0
      simp only [z, hs, Option.elim_some]
      exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr h0
  have hos : ∀ s, fibreSNCOrder α (x : W) F hF σF s = W.ord (σx (ψe (z s))) (x : W) := by
    intro s
    unfold fibreSNCOrder
    cases hs : σF s with
    | none => simp [z, hs]
    | some a =>
      simp only [z, hs, Option.elim_some]
      rfl
  have hordprod : ∀ k : Fin r → ℕ, W.ord (∏ s, (σx (ψe (z s))) ^ (k s)) (x : W) =
      ∑ s, (k s : ℤ) * fibreSNCOrder α (x : W) F hF σF s := by
    intro k
    have h1 : ∏ s, (σx (ψe (z s))) ^ (k s) =
        ((∏ s, (Units.mk0 _ (hzne s)) ^ (k s : ℤ) : W.functionFieldˣ) : W.functionField) := by
      rw [Units.coe_prod]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [h1, scheme_ord_prod_zpow]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Units.val_mk0, hos]
  have hσQ0 : σx Q.det ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hQ0
  have hne_lam : ψ' lam ≠ 0 := by
    intro h0
    have h1 := hlamW
    rw [h0, zero_mul] at h1
    exact Units.ne_zero _ h1
  have hprodne : ∀ k : Fin r → ℕ, ∏ s, (σx (ψe (z s))) ^ (k s) ≠ 0 := fun k =>
    Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ (hzne s)
  have hunitW : W.ord (σx (ψe ((u' : T.presheaf.stalk (α (x : W))) * u))) (x : W) = 0 := by
    have h := scheme_ord_stalk_unit (x : W) (Units.map ψe.toRingHom.toMonoidHom (u' * u))
    rw [Units.coe_map] at h
    exact h
  have hune : σx (ψe ((u' : T.presheaf.stalk (α (x : W))) * u)) ≠ 0 := by
    have hu1 : IsUnit (ψe ((u' : T.presheaf.stalk (α (x : W))) * u)) :=
      ((u' * u).isUnit).map ψe
    exact (hu1.map σx).ne_zero
  have hordlam : W.ord (ψ' lam) (x : W) = ∑ s, L s * fibreSNCOrder α (x : W) F hF σF s := by
    have h := congrArg (fun t => W.ord t (x : W)) hW'
    simp only at h
    rw [Scheme.ord_mul hne_lam (hprodne N), Scheme.ord_mul hune (hprodne M), hordprod N,
      hordprod M, hunitW, zero_add] at h
    have hsplit : ∑ s, L s * fibreSNCOrder α (x : W) F hF σF s =
        ∑ s, (M s : ℤ) * fibreSNCOrder α (x : W) F hF σF s -
          ∑ s, (N s : ℤ) * fibreSNCOrder α (x : W) F hF σF s := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hLMN s]
      ring
    linarith
  -- the coefficient at x and the logarithmic pole bound for the fibre coordinates
  obtain ⟨k, hk, hkprime⟩ := scheme_regular_ringOrd_and_primeOrd_nat x Q.det hQ0
  have hkσ : W.ord (σx Q.det) (x : W) = k := hkprime
  rw [cartierCoefficient_eq_ord hlocσ, hlamW, Scheme.ord_mul hne_lam (pow_ne_zero _ hσQ0),
    scheme_ord_pow hσQ0, hordlam, hkσ]
  have hbound := dvr_derivation_jacobian_order_bound
    (fun j => etaleCoordinateDerivation ce hce j)
    (fun i' => ψe (fe (MvPolynomial.X (Fin.castAdd e i')))) hrow
  choose m hm hprime using fun i' => scheme_regular_ringOrd_and_primeOrd_nat x
    (ψe (fe (MvPolynomial.X (Fin.castAdd e i')))) (hrow i')
  change ∑ i', Ring.ord (W.presheaf.stalk (x : W)) (ψe (fe (MvPolynomial.X (Fin.castAdd e i')))) ≤
    1 + Ring.ord (W.presheaf.stalk (x : W)) Q.det at hbound
  simp_rw [hm] at hbound
  rw [hk, ← Nat.cast_sum, ← Nat.cast_one, ← Nat.cast_add] at hbound
  have hnat : ∑ i', m i' ≤ 1 + k := by exact_mod_cast hbound
  -- the selected member coordinates
  let σ'' : Fin r → Option (Fin n) := fun s =>
    (σF s).bind fun a => if h : (a : ℕ) < n then some ⟨a, h⟩ else none
  have hσ''inj : ∀ i j a, σ'' i = some a → σ'' j = some a → i = j := by
    intro i j a hi hj
    have key : ∀ k, σ'' k = some a → σF k = some (Fin.castAdd e a) := by
      intro k hk
      cases hs : σF k with
      | none => simp [σ'', hs] at hk
      | some b =>
        simp only [σ'', hs, Option.bind_some] at hk
        split_ifs at hk with h
        · simp only [Option.some.injEq] at hk
          congr 1
          exact Fin.ext (by rw [← hk]; rfl)
    exact hFsnc.1 i j _ (key i hi) (key j hj)
  have hosel : ∀ s, fibreSNCOrder α (x : W) F hF σF s =
      (σ'' s).elim 0 (fun i' => (m i' : ℤ)) := by
    intro s
    unfold fibreSNCOrder
    cases hs : σF s with
    | none => simp [σ'', hs]
    | some a =>
      have ha := hσF s a hs
      simp only [Option.elim_some, σ'', hs, Option.bind_some, ha, ↓reduceDIte]
      rw [← hprime ⟨a, ha⟩]
      rfl
  have hsel := option_selected_sum_le σ'' hσ''inj (fun i' => (m i' : ℤ)) (fun i' => by positivity)
  simp_rw [← hosel] at hsel
  have hcast : ((∑ i', m i' : ℕ) : ℤ) ≤ 1 + (k : ℤ) := by exact_mod_cast hnat
  push_cast at hcast
  have hsumo : ∑ s, fibreSNCOrder α (x : W) F hF σF s ≤ 1 + (k : ℤ) := hsel.trans hcast
  have hd0 : (0 : ℤ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_le_mul_of_nonneg_left hsumo hd0]

end ChainRule

end MixedFujita
