/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltProductRestrictionStatements
public import MixedFujita.EtaleDomainNormality
public import MixedFujita.NormalSectionsAndStein
public import MixedFujita.NormalCodimensionOneCharts
public import MixedFujita.SmoothKawamataNumericalFreeness
public import MixedFujita.SNCBoundaryDiscrepancy
public import MixedFujita.KltFibreLogDiscrepancy
public import MixedFujita.RealizationThresholdReduction

/-!
The product P = Spec B ×_K Y of a normal variety with a domain of finite type with formally
étale coordinates, and its product pair (step 15, restriction to the fibres of the product).

* **Normality**: over an affine open V of Y the functions on P are B ⊗_K Γ(V), which is étale over
  K[u] ⊗_K Γ(V) ≅ Γ(V)[u], a normal domain; an étale domain over a normal domain is normal
  (`etaleDomain_isIntegrallyClosed`), so every stalk of P is integrally closed
  (`specFibreProduct_stalk_isIntegrallyClosed`), and P has charts at its codimension-one points
  (`specFibreProduct_codimOneChartCovered`, via `normal_codimOneChartCovered`).
* **Codimension**: the projection P → Y is flat, hence generalizing, so the image of a point has
  at most its codimension (`coheight_le_coheight_of_generalizingMap`).
* **Effective boundary**: the boundary of the product pair (product chart, pulled back form and
  divisor) is effective (`fibreProductPair_logPairBoundaryEffective`): at a prime divisor of P the
  image in Y is the generic point or a prime divisor, the product charts over a chart of Y there
  have the pulled back canonical equations (`fibreProductChart_canonicalEquation`), and the
  boundary condition on Y says that δ u^{−d} is regular at the image for a local equation δ of D₀
  and the form u in that chart, which stays regular after pulling back.
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

section Polynomial

/-- A polynomial ring in finitely many variables over a normal domain is normal. -/
theorem mvPolynomial_fin_isIntegrallyClosed {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : ∀ m : ℕ, IsIntegrallyClosed (MvPolynomial (Fin m) R)
  | 0 => IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | m + 1 => by
    have := mvPolynomial_fin_isIntegrallyClosed (R := R) m
    exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R m).symm.toRingEquiv

end Polynomial

section Tensor

variable {K : Type u} [Field K] {B R : Type u} [CommRing B] [Algebra K B] [CommRing R]
  [Algebra K R]

/-- **Normality of B ⊗_K R**: for a normal domain R over K and a K-algebra B of finite type with
formally étale coordinates, a domain B ⊗_K R is normal, being étale over K[u] ⊗_K R ≅ R[u]. -/
theorem tensor_isIntegrallyClosed_of_formallyEtale [Algebra.FiniteType K B] {e : ℕ}
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale) [IsDomain R]
    [IsIntegrallyClosed R] [IsDomain (B ⊗[K] R)] : IsIntegrallyClosed (B ⊗[K] R) := by
  classical
  let _ : Algebra (MvPolynomial (Fin e) K) B := φ.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin e) K) B :=
    IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  have : Algebra.FormallyEtale (MvPolynomial (Fin e) K) B := RingHom.formallyEtale_algebraMap.mp hφ
  have : Algebra.FiniteType (MvPolynomial (Fin e) K) B :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ B
  have : Algebra.FinitePresentation (MvPolynomial (Fin e) K) B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale (MvPolynomial (Fin e) K) B := ⟨inferInstance, inferInstance⟩
  -- the base change K[u] ⊗ R → B ⊗ R of K[u] → B
  let R' := MvPolynomial (Fin e) K ⊗[K] R
  let M : R' →ₐ[K] B ⊗[K] R := Algebra.TensorProduct.map φ (AlgHom.id K R)
  let _ : Algebra R' (B ⊗[K] R) := M.toRingHom.toAlgebra
  let _ : Algebra R (B ⊗[K] R) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra R R' := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower (MvPolynomial (Fin e) K) R' (B ⊗[K] R) :=
    IsScalarTower.of_algebraMap_eq fun s => by
      change (φ s) ⊗ₜ[K] (1 : R) = M (s ⊗ₜ 1)
      rfl
  have : IsScalarTower K R' (B ⊗[K] R) :=
    IsScalarTower.of_algebraMap_eq fun k => (M.commutes k).symm
  have : IsScalarTower R R' (B ⊗[K] R) :=
    IsScalarTower.of_algebraMap_eq fun g => by
      change (1 : B) ⊗ₜ[K] g = M (1 ⊗ₜ g)
      change (1 : B) ⊗ₜ[K] g = φ 1 ⊗ₜ[K] g
      rw [map_one]
  have : IsScalarTower K R (B ⊗[K] R) :=
    IsScalarTower.of_algebraMap_eq fun k => by
      change algebraMap K _ k = (1 : B) ⊗ₜ[K] algebraMap K R k
      rw [Algebra.TensorProduct.algebraMap_apply, ← mul_one (algebraMap K B k),
        ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have hpo : Algebra.IsPushout (MvPolynomial (Fin e) K) B R' (B ⊗[K] R) :=
    (Algebra.IsPushout.comp_iff K (MvPolynomial (Fin e) K) R (T := B) (S' := R')
      (T' := B ⊗[K] R)).mp inferInstance
  have hpo' : Algebra.IsPushout (MvPolynomial (Fin e) K) R' B (B ⊗[K] R) := hpo.symm
  have : Algebra.Etale R' (R' ⊗[MvPolynomial (Fin e) K] B) := inferInstance
  have hEt : Algebra.Etale R' (B ⊗[K] R) :=
    Algebra.Etale.of_equiv (R := R') (A := R' ⊗[MvPolynomial (Fin e) K] B)
      (Algebra.IsPushout.equiv (MvPolynomial (Fin e) K) R' B (B ⊗[K] R))
  -- K[u] ⊗ R ≅ R[u] is a normal domain
  let ε : R' ≃+* MvPolynomial (Fin e) R :=
    (Algebra.TensorProduct.comm K (MvPolynomial (Fin e) K) R).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv K R).toRingEquiv
  have : IsDomain R' := MulEquiv.isDomain (MvPolynomial (Fin e) R) ε.toMulEquiv
  have : IsIntegrallyClosed (MvPolynomial (Fin e) R) := mvPolynomial_fin_isIntegrallyClosed e
  have : IsIntegrallyClosed R' := IsIntegrallyClosed.of_equiv ε.symm
  exact etaleDomain_isIntegrallyClosed (R := R') (S := B ⊗[K] R)

end Tensor

section Normality

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [IsDomain B]
  [Algebra K B] [Algebra.FiniteType K B] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] specFibreProduct_isIntegral specFibreProduct_preimage_nonempty
  specAlgebraOver cartierBaseOpenAlgebra structureSectionsAlgebra specFibreProductOverAlgebra
  specFibreProductOverField specFibreProduct_isScalarTower

/-- **The fibre product Spec B ×_K Y is normal** for a normal Y and a domain B of finite type
with formally étale coordinates. -/
theorem specFibreProduct_stalk_isIntegrallyClosed {e : ℕ} (φ : MvPolynomial (Fin e) K →ₐ[K] B)
    (hφ : φ.toRingHom.FormallyEtale) (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (p : specFibreProduct K B Y) :
    IsIntegrallyClosed ((specFibreProduct K B Y).presheaf.stalk p) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (specFibreProductSnd K B Y p)) isOpen_univ
  have hVa : IsAffineOpen V := hV
  have : Nonempty V := ⟨⟨_, hpV⟩⟩
  have : IsAffineHom (specFibreProductSnd K B Y) := MorphismProperty.pullback_snd _ _ inferInstance
  have hW : IsAffineOpen (specFibreProductSnd K B Y ⁻¹ᵁ V) := hVa.preimage _
  have hp : p ∈ specFibreProductSnd K B Y ⁻¹ᵁ V := hpV
  have : IsIntegrallyClosed Γ(Y, V) := normal_sections_isIntegrallyClosed hnorm V
  let ε := specFibreProductSectionsEquiv (K := K) (B := B) hVa
  have : IsDomain (B ⊗[K] Γ(Y, V)) :=
    MulEquiv.isDomain Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) ε.toRingEquiv.toMulEquiv
  have hB := tensor_isIntegrallyClosed_of_formallyEtale (R := Γ(Y, V)) φ hφ
  have : IsIntegrallyClosed Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V) :=
    IsIntegrallyClosed.of_equiv ε.toRingEquiv
  let := TopCat.Presheaf.algebra_section_stalk (specFibreProduct K B Y).presheaf
    (⟨p, hp⟩ : specFibreProductSnd K B Y ⁻¹ᵁ V)
  have := hW.isLocalization_stalk ⟨p, hp⟩
  exact isIntegrallyClosed_of_isLocalization ((specFibreProduct K B Y).presheaf.stalk p)
    (hW.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl
    (hW.primeIdealOf ⟨p, hp⟩).asIdeal.primeCompl_le_nonZeroDivisors

variable [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

omit [IsAlgClosed K] [IsDomain B] [IsIntegral Y] [IsLocallyNoetherian Y] in
/-- The fibre product is locally of finite type over K. -/
theorem specFibreProduct_locallyOfFiniteType :
    LocallyOfFiniteType (specFibreProduct K B Y ↘ Spec (CommRingCat.of K)) := by
  have := specAlgebra_locallyOfFiniteType (K := K) (B := B)
  have : LocallyOfFiniteType (specFibreProductFst K B Y) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  change LocallyOfFiniteType (specFibreProductFst K B Y ≫
    (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)))
  infer_instance

/-- **The codimension-one points of the fibre product lie in étale charts.** -/
theorem specFibreProduct_codimOneChartCovered {n e : ℕ} (cY : EtaleChart K Y n)
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
    (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    CodimOneChartCovered (n + e) K (specFibreProduct K B Y) := by
  have := specFibreProduct_locallyOfFiniteType (K := K) (B := B) (Y := Y)
  exact normal_codimOneChartCovered (K := K)
    (etaleChart_topologicalKrullDim (fibreProductEtaleChart cY φ hφ))
    (specFibreProduct_stalk_isIntegrallyClosed φ hφ hnorm)

omit [IsAlgClosed K] [IsDomain B] [IsIntegral Y] [IsLocallyNoetherian Y] in
/-- The fibre product is locally noetherian. -/
theorem specFibreProduct_isLocallyNoetherian : IsLocallyNoetherian (specFibreProduct K B Y) := by
  have := specFibreProduct_locallyOfFiniteType (K := K) (B := B) (Y := Y)
  exact LocallyOfFiniteType.isLocallyNoetherian (specFibreProduct K B Y ↘ Spec (CommRingCat.of K))

end Normality

section Codimension

/-- A generalizing morphism does not increase codimension: the image of a point has at most its
codimension. -/
theorem coheight_le_coheight_of_generalizingMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : GeneralizingMap f) (a : X) : Order.coheight (f a) ≤ Order.coheight a := by
  suffices h : ∀ (m : ℕ) (a : X), (m : ℕ∞) ≤ Order.coheight (f a) → (m : ℕ∞) ≤ Order.coheight a by
    exact ENat.forall_natCast_le_iff_le.mp fun m hm => h m a hm
  intro m
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    obtain ⟨p, hhead, hlen⟩ := Order.exists_series_of_le_coheight (f a) h
    -- the second term of the series
    have hlen0 : p.length ≠ 0 := by omega
    let b : Y := p 1
    have h01 : (0 : Fin (p.length + 1)) < 1 := by
      rw [Fin.lt_def, Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      omega
    have hab : f a < b := by
      have h0 : p 0 = f a := hhead
      rw [← h0]
      exact p.strictMono h01
    have hmb : (m : ℕ∞) ≤ Order.coheight b := by
      have h1 := Order.length_le_coheight_head (p := p.tail hlen0)
      rw [RelSeries.head_tail] at h1
      have hl : ((p.tail hlen0).length : ℕ∞) = m := by
        rw [RelSeries.tail_length]
        simp [hlen]
      rw [hl] at h1
      exact h1
    -- lift the generization
    obtain ⟨a', ha'a, hfa'⟩ := hf (a := a) (b := b) hab.le
    have haa' : a < a' := by
      refine lt_of_le_not_ge ha'a fun h => ?_
      have h2 : f a ⤳ f a' := h.map f.continuous
      rw [hfa'] at h2
      exact hab.not_ge h2
    have hm' := ih a' (by rw [hfa']; exact hmb)
    have h3 := Order.coheight_add_one_le haa'
    calc ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.coheight a' + 1 := by gcongr
      _ ≤ Order.coheight a := h3

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))]

attribute [local instance] specAlgebraOver specFibreProductOverAlgebra specFibreProductOverField

/-- The second projection of the fibre product is flat. -/
theorem specFibreProductSnd_flat : Flat (specFibreProductSnd K B Y) := by
  have : Flat (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) := by
    change Flat (Spec.map (CommRingCat.ofHom (algebraMap K B)))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The image in Y of a point of the fibre product has at most its codimension. -/
theorem specFibreProduct_coheight_snd_le (p : specFibreProduct K B Y) :
    Order.coheight (specFibreProductSnd K B Y p) ≤ Order.coheight p := by
  have := specFibreProductSnd_flat (K := K) (B := B) (Y := Y)
  exact coheight_le_coheight_of_generalizingMap _ (Flat.generalizingMap _) p

end Codimension

section Boundary

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [IsDomain B]
  [Algebra K B] [Algebra.FiniteType K B] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] {n e : ℕ}

attribute [local instance] specFibreProduct_isIntegral specFibreProduct_preimage_nonempty
  specAlgebraOver specFibreProductOverAlgebra specFibreProductOverField
  specFibreProductSnd_isDominant specFibreProductSnd_isOver
  cartierBaseOpenAlgebra functionFieldBaseAlgebra specFibreProduct_isLocallyNoetherian

/-- The germ of a unit section has order zero at the points of its open. -/
theorem scheme_ord_germ_unit_eq_zero {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} [Nonempty U] (w : Γ(X, U)ˣ) {x : X} (hx : x ∈ U) :
    X.ord (X.germToFunctionField U (w : Γ(X, U))) x = 0 := by
  have h1 := TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg (w : Γ(X, U)) hx
  have h2 := TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg
    ((w⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) hx
  have hmul : X.germToFunctionField U ((w⁻¹ : Γ(X, U)ˣ) : Γ(X, U)) =
      (X.germToFunctionField U (w : Γ(X, U)))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]
  rw [hmul, TauCeti.AlgebraicGeometry.Scheme.ord_inv] at h2
  omega

/-- A rational function of Y regular at the image of a point of P pulls back to a function of
nonnegative order. -/
theorem specFibreProduct_ord_pullback_nonneg (p : specFibreProduct K B Y)
    (f : Y.functionField)
    (hf : f ∈ (algebraMap (Y.presheaf.stalk (specFibreProductSnd K B Y p)) Y.functionField).range) :
    0 ≤ (specFibreProduct K B Y).ord
      ((dominantFunctionFieldMap (specFibreProductSnd K B Y)).hom f) p := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨U, hU, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have : Nonempty (specFibreProductSnd K B Y ⁻¹ᵁ U) := ⟨⟨p, hU⟩⟩
  rw [← ha, Scheme.algebraMap_germ_eq_germToFunctionField,
    dominantFunctionFieldMap_germ (specFibreProductSnd K B Y) U _ le_rfl s]
  exact TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg _ hU

/-- **The boundary of the product pair is effective.** -/
theorem fibreProductPair_logPairBoundaryEffective (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y)
    (heff : LogPairBoundaryEffective cY fY d D₀) (hcov : CodimOneChartCovered n K Y)
    (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (φ : MvPolynomial (Fin e) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale) :
    LogPairBoundaryEffective (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B) D₀) := by
  classical
  intro c p hpc hcoh
  set q := specFibreProductSnd K B Y p with hq
  have hql : Order.coheight q ≤ 1 := hcoh ▸ specFibreProduct_coheight_snd_le p
  -- a chart of Y at q
  obtain ⟨cq, hcq⟩ : ∃ c' : EtaleChart K Y n, q ∈ c'.U := by
    rcases (show Order.coheight q = 0 ∨ Order.coheight q = 1 by
      cases h : Order.coheight q using ENat.recTopCoe with
      | top => rw [h] at hql; exact absurd hql (by decide)
      | coe k =>
        rw [h] at hql
        have : k ≤ 1 := by exact_mod_cast hql
        interval_cases k <;> simp) with h0 | h1
    · have hmax : IsMax q := Order.coheight_eq_zero.mp h0
      have hgen : q = genericPoint Y := by
        have h1 : genericPoint Y ⤳ q := (genericPoint_spec Y).specializes (Set.mem_univ _)
        have h2 : q ≤ genericPoint Y := h1
        have h3 : genericPoint Y ≤ q := hmax h2
        exact (h1.antisymm h3).symm.eq
      have : Nonempty cY.U := cY.nonempty
      exact ⟨cY, hgen ▸ genericPoint_mem cY.U⟩
    · exact hcov q h1
  -- the product chart over cq contains p
  set cq' := fibreProductEtaleChart (B := B) cq φ hφ
  have hpq' : p ∈ cq'.U := hcq
  -- the form in the chart cq and a local equation of D₀ at q
  set u : Y.functionFieldˣ := fY * etaleChartCanonicalEquation cY cq with hu
  obtain ⟨δ, hδ⟩ := D₀.exists_isLocalEquationAt q
  -- δ u^{-d} is regular at q
  have hreg : ((δ * (u ^ d)⁻¹ : Y.functionFieldˣ) : Y.functionField) ∈
      (algebraMap (Y.presheaf.stalk q) Y.functionField).range := by
    by_cases h1 : Order.coheight q = 1
    · apply mem_range_stalk_of_ord_nonneg hnorm q h1
      have hineq := heff cq q hcq h1
      rw [cartierCoefficient_eq_ord hδ] at hineq
      rw [Units.val_mul, Y.ord_mul (Units.ne_zero _) (Units.ne_zero _), Units.val_inv_eq_inv_val,
        TauCeti.AlgebraicGeometry.Scheme.ord_inv, Units.val_pow_eq_pow_val,
        scheme_ord_pow (Units.ne_zero _)]
      linarith
    · have h0 : Order.coheight q = 0 := by
        rcases (show Order.coheight q = 0 ∨ Order.coheight q = 1 by
          cases h : Order.coheight q using ENat.recTopCoe with
          | top => rw [h] at hql; exact absurd hql (by decide)
          | coe k =>
            rw [h] at hql
            have : k ≤ 1 := by exact_mod_cast hql
            interval_cases k <;> simp) with h0 | h1'
        · exact h0
        · exact absurd h1' h1
      have hmax : IsMax q := Order.coheight_eq_zero.mp h0
      have hgen : q = genericPoint Y := by
        have h1 : genericPoint Y ⤳ q := (genericPoint_spec Y).specializes (Set.mem_univ _)
        have h2 : q ≤ genericPoint Y := h1
        have h3 : genericPoint Y ≤ q := hmax h2
        exact (h1.antisymm h3).symm.eq
      obtain ⟨b, hb⟩ := exists_stalk_eq_of_eq_genericPoint (K := K) hgen
        ((δ * (u ^ d)⁻¹ : Y.functionFieldˣ) : Y.functionField)
      exact ⟨b, hb⟩
  have hpull := specFibreProduct_ord_pullback_nonneg p _ hreg
  -- the form of the product pair in the chart c
  set σ := (dominantFunctionFieldMap (specFibreProductSnd K B Y)).hom
  have hform : (specFibreProduct K B Y).ord ((fibreProductPairUnit (K := K) (B := B) fY *
      etaleChartCanonicalEquation (fibreProductEtaleChart cY φ hφ) c : (specFibreProduct K B Y).functionFieldˣ) :
        (specFibreProduct K B Y).functionField) p = (specFibreProduct K B Y).ord (σ (u : Y.functionField)) p := by
    obtain ⟨w, hw⟩ := etaleChartCanonicalEquation_transition (fibreProductEtaleChart cY φ hφ) c cq'
    let := integral_opens_inter_nonempty (specFibreProduct K B Y) c.U cq'.U
    have hwe : ((etaleChartCanonicalEquation (fibreProductEtaleChart cY φ hφ) c :
        (specFibreProduct K B Y).functionFieldˣ) : (specFibreProduct K B Y).functionField) = (specFibreProduct K B Y).germToFunctionField (c.U ⊓ cq'.U) (w : _) *
          (etaleChartCanonicalEquation (fibreProductEtaleChart cY φ hφ) cq' : (specFibreProduct K B Y).functionField) := by
      rw [hw, Units.val_mul, Units.coe_map]
      rfl
    have hpr := fibreProductChart_canonicalEquation (K := K) (B := B) cY cq φ hφ
    have hw0 := scheme_ord_germ_unit_eq_zero w (show p ∈ c.U ⊓ cq'.U from ⟨hpc, hpq'⟩)
    have hfP : ((fibreProductPairUnit (K := K) (B := B) fY : (specFibreProduct K B Y).functionFieldˣ) :
        (specFibreProduct K B Y).functionField) = σ (fY : Y.functionField) := rfl
    rw [Units.val_mul, hwe, hfP]
    have hne1 : (specFibreProduct K B Y).germToFunctionField (c.U ⊓ cq'.U) (w : _) ≠ 0 :=
      ((Units.isUnit w).map _).ne_zero
    have hne2 : σ (fY : Y.functionField) ≠ 0 := (map_ne_zero _).mpr (Units.ne_zero _)
    have hne3 : ((etaleChartCanonicalEquation (fibreProductEtaleChart cY φ hφ) cq' :
        (specFibreProduct K B Y).functionFieldˣ) : (specFibreProduct K B Y).functionField) ≠ 0 := Units.ne_zero _
    rw [show σ (fY : Y.functionField) * ((specFibreProduct K B Y).germToFunctionField (c.U ⊓ cq'.U) (w : _) *
        (etaleChartCanonicalEquation (fibreProductEtaleChart cY φ hφ) cq' : (specFibreProduct K B Y).functionField)) =
        (specFibreProduct K B Y).germToFunctionField (c.U ⊓ cq'.U) (w : _) * (σ (fY : Y.functionField) *
          (etaleChartCanonicalEquation (fibreProductEtaleChart cY φ hφ) cq' : (specFibreProduct K B Y).functionField))
        by ring]
    rw [(specFibreProduct K B Y).ord_mul hne1 (mul_ne_zero hne2 hne3), hw0, zero_add]
    congr 1
    rw [hu, Units.val_mul, map_mul, hpr]
    rfl
  -- the divisor of the product pair at p
  have hD : cartierCoefficient (fibreProductPairDivisor (K := K) (B := B) D₀) p =
      (specFibreProduct K B Y).ord (σ (δ : Y.functionField)) p := by
    have h := cartierPullback_isLocalEquationAt (specFibreProductSnd K B Y) D₀ p hδ
    unfold fibreProductPairDivisor
    rw [cartierCoefficient_eq_ord h]
    rfl
  rw [hform, hD]
  have hσu : σ (u : Y.functionField) ≠ 0 := (map_ne_zero _).mpr (Units.ne_zero _)
  have hσδ : σ (δ : Y.functionField) ≠ 0 := (map_ne_zero _).mpr (Units.ne_zero _)
  rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀,
    map_pow, (specFibreProduct K B Y).ord_mul hσδ (inv_ne_zero (pow_ne_zero _ hσu)),
    TauCeti.AlgebraicGeometry.Scheme.ord_inv, scheme_ord_pow hσu] at hpull
  linarith

end Boundary

end MixedFujita
