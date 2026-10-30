/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltHyperplaneResidue

/-!
Adjunction along the strict transform of a hyperplane of the product, in the weak model form of
badness (step 15, the klt restriction theorem).

Let ρ : T → P = Spec B ×_K Y be a smooth model of the product pair, c an SNC chart of T at a point
t' over (w, y) in which the strict transform ξ_{s₀} of the hyperplane u_0 = 0 is y_0 = 0 and
another member ξ_j is y_1 = 0, U = Spec(Γ(T, c.U)/(y_0)) → H = Spec(B/(u_0)) ×_K Y the test model
and e a component of y_1 = 0 on U through t'. The coefficient of the discrepancy divisor of U → H
along e is L_j − d h_j (`klt_hyperplane_adjunction_weakBad`): the local equation of the
discrepancy divisor of ρ is a unit times w_0^d times the monomial of the SNC chart, by the local
products, and its residue along ξ_{s₀} is ± w̄_0^d times the local equation on U
(`hyperplaneTest_jacobian_residue`, `hyperplaneTest_constant_residue`).
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

section Adjunction

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [IsDomain B]
  [Algebra K B] [Algebra.FiniteType K B] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  {n e : ℕ}

attribute [local instance] specAlgebraOver specFibreProductOverAlgebra specFibreProductOverField
  specFibreProduct_isIntegral specFibreProduct_preimage_nonempty specFibreProductSnd_isDominant
  specFibreProductSnd_isOver specFibreProduct_isLocallyNoetherian specFibreProductFst_isOver
  hyperplaneTestInclusion_isOver

omit [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
set_option maxHeartbeats 3200000 in
/-- **Adjunction along the strict transform of the hyperplane u_0 = 0 of the product.** Let
ρ : T → P = Spec B ×_K Y be a smooth model of the product pair whose discrepancy divisor and the
divisor of ρ*u_0 are supported on an SNC family ξ, c an SNC chart at a point t' over (w, y) in
which the strict transform ξ_{s₀} is y_0 = 0 (ρ a local isomorphism there, coefficients 0 and 1)
and a member ξ_j is y_1 = 0, and a family g with ρ*g_k ∈ y_1^a in the quotient by y_0 near t'.
If M (d + L_j − d h_j) ≤ d a for the coefficients L_j of the discrepancy divisor and h_j of ρ*u_0
along ξ_j, the restriction of g to H = Spec(B/(u_0)) ×_K Y has threshold at most 1/M at (w, y) in
the weak model form, with the test model Spec(Γ(T, c.U)/(y_0)) → H (`hyperplaneTestMap`). -/
theorem klt_hyperplane_adjunction_weakBad (hn : 1 ≤ n) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (V : Y.Opens) [Nonempty V]
    (δ : Y.functionFieldˣ) (hδ : ∀ y ∈ V, D₀.IsLocalEquationAt y δ)
    (φ : MvPolynomial (Fin (e + 1)) K →ₐ[K] B) (hφ : φ.toRingHom.FormallyEtale)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
    {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension (n + (e + 1)) (T ↘ Spec (CommRingCat.of K))]
    (fT : T ⟶ specFibreProduct K B Y) [IsDominant fT] [fT.IsOver (Spec (CommRingCat.of K))]
    (hfT : Function.Bijective (dominantFunctionFieldAlgHom (K := K) fT))
    (cT : EtaleChart K T (n + (e + 1))) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hLsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT
        (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
        (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover) (z : T) = 0)
    (c : EtaleChart K T (n + (e + 1))) (σc : Fin r → Option (Fin (n + (e + 1))))
    (hc : IsSNCChart c ξ σc) (s₀ j : Fin r) (hσ₀ : σc s₀ = some 0) (hσj : σc j = some 1)
    (hξ₀c : ξ s₀ ∈ c.U) (w₀ : Γ(T, c.U))
    (hw₀ : modelChartAlgHom (K := K) (fT ≫ specFibreProductFst K B Y) c.U (φ (MvPolynomial.X 0)) =
      c.coords (MvPolynomial.X 0) * w₀)
    (tT : T.functionFieldˣ)
    (htT : (tT : T.functionField) = T.germToFunctionField c.U (c.coords (MvPolynomial.X 0) * w₀))
    (hHsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (principalCartierDivisor T tT) (z : T) = 0)
    (hL₀ : cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT
        (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
        (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover) (ξ s₀) = 0)
    (hh₀ : cartierCoefficient (principalCartierDivisor T tT) (ξ s₀) = 1)
    (hbij : Function.Bijective (fT.stalkMap (ξ s₀)))
    (hgen : fT (ξ s₀) ⤳ specFibreProductMap (Y := Y)
      (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))
        (genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y)))
    (t' : T) (ht'c : t' ∈ c.U) (ht'0 : t' ∈ closure ({ξ s₀} : Set T))
    (ht'j : t' ∈ closure ({ξ j} : Set T)) (w : B →ₐ[K] K)
    (hw0 : ∀ b ∈ Ideal.span {φ (MvPolynomial.X 0)}, w b = 0) (y : Y)
    (hx : fT t' = specFibreProductFibre (V := Y) w y)
    (hcV : c.U ≤ fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ V))
    {J : Type} (g : J → Γ(specFibreProduct K B Y, specFibreProductSnd K B Y ⁻¹ᵁ V)) (a : ℕ)
    (hga : ∀ k, ∃ q Vk : hyperplaneTestRing c,
      Vk ∉ (c.isAffine.primeIdealOf ⟨t', ht'c⟩).asIdeal.map (Ideal.Quotient.mk _) ∧
      Ideal.Quotient.mk _ (fT.appLE _ c.U hcV (g k)) * Vk =
        Ideal.Quotient.mk _ (c.coords (MvPolynomial.X 1)) ^ a * q)
    (M : ℕ)
    (hineq : (M : ℤ) * ((d : ℤ) + cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT
        (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
        (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover) (ξ j) -
        (d : ℤ) * cartierCoefficient (principalCartierDivisor T tT) (ξ j)) ≤ (d : ℤ) * a) :
    ModelThresholdWeakBadAt
      (fibreProductEtaleChart cY (hyperplaneCoords φ) (hyperplaneCoords_formallyEtale φ hφ))
      (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) D₀)
      (specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w hw0) y)
      (fun k => (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y).germToFunctionField
        (specFibreProductSnd K _ Y ⁻¹ᵁ V)
        ((specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).appLE
          (specFibreProductSnd K B Y ⁻¹ᵁ V) (specFibreProductSnd K _ Y ⁻¹ᵁ V) (fun x hx => by
            change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
              specFibreProductSnd K B Y) x ∈ V
            rw [specFibreProductMap_snd]
            exact hx) (g k))) M := by
  classical
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + (e + 1)) _
  have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)) := inferInstance
  -- the hyperplane and its closed immersion
  let θ : B →ₐ[K] B ⧸ Ideal.span {φ (MvPolynomial.X 0)} :=
    Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})
  haveI hιH : IsClosedImmersion (specFibreProductMap (Y := Y) θ) :=
    specFibreProductMap_isClosedImmersion θ (Ideal.Quotient.mkₐ_surjective K _)
  -- the test model
  haveI hprime : (Ideal.span {c.coords (MvPolynomial.X 0)}).IsPrime :=
    span_coordinate_isPrime_of_isSNCChart c ξ σc hc s₀ 0 hσ₀ hξ₀c
  have hprimeEq := span_coordinate_eq_primeIdealOf_of_isSNCChart c ξ σc hc s₀ 0 hσ₀ hξ₀c
  have hsq := hyperplaneTestMap_comm c fT φ w₀ hw₀
  have hζ := hyperplaneTestInclusion_genericPoint c (ξ s₀) hξ₀c hprimeEq
  have hσgen : hyperplaneTestMap c fT φ w₀ hw₀ (genericPoint _) = genericPoint _ :=
    genericPoint_eq_of_comm _ fT _ _ hsq (by rw [hζ]; exact hgen)
  haveI hσdom : IsDominant (hyperplaneTestMap c fT φ w₀ hw₀) :=
    isDominant_of_genericPoint_eq _ hσgen
  haveI hσover := hyperplaneTestMap_isOver c fT φ w₀ hw₀
  haveI : SurjectiveOnStalks (hyperplaneTestInclusion c) := by
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mkₐ K (Ideal.span {c.coords (MvPolynomial.X 0)})).toRingHom)) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    unfold hyperplaneTestInclusion specAlgebraHom
    infer_instance
  have hσbij : Function.Bijective (dominantFunctionFieldAlgHom (K := K)
      (hyperplaneTestMap c fT φ w₀ hw₀)) :=
    dominantFunctionFieldMap_bijective_of_comm _ fT _ _ hsq (by rw [hζ]; exact hbij)
  -- the test model is smooth with the coordinates y_1, …, y_N
  have hfeU := hyperplaneCoords_formallyEtale c.coords c.formallyEtale
  have hetU := etaleChart_hyperplaneCoords_etale c
  haveI hsmU : Algebra.Smooth K (hyperplaneTestRing c) := by
    let _ : Algebra (MvPolynomial (Fin (n + e)) K) (hyperplaneTestRing c) :=
      (hyperplaneCoords c.coords).toRingHom.toAlgebra
    have : IsScalarTower K (MvPolynomial (Fin (n + e)) K) (hyperplaneTestRing c) :=
      IsScalarTower.of_algebraMap_eq fun k => ((hyperplaneCoords c.coords).commutes k).symm
    have hEt : Algebra.Etale (MvPolynomial (Fin (n + e)) K) (hyperplaneTestRing c) := hetU
    have : Algebra.Smooth K (MvPolynomial (Fin (n + e)) K) := {}
    exact Algebra.Smooth.comp K (MvPolynomial (Fin (n + e)) K) (hyperplaneTestRing c)
  haveI hrelU := specAlgebraOver_smoothOfRelativeDimension (K := K) (hyperplaneTestRing c)
    (hyperplaneCoords c.coords) hfeU
  have : IsNoetherianRing (hyperplaneTestRing c) := by
    have := sectionsBaseOpen_finiteType (K := K) c.isAffine
    exact Algebra.FiniteType.isNoetherianRing K _
  let cU := specAlgebraEtaleChart (K := K) (hyperplaneCoords c.coords) hfeU
  -- the point over t' and the point over (w, y)
  let Q := (c.isAffine.primeIdealOf ⟨t', ht'c⟩).asIdeal
  have hz₀Q : c.coords (MvPolynomial.X 0) ∈ Q :=
    sncChart_coordinate_mem_point_prime c ξ σc hc s₀ 0 hσ₀ t' ht'c ht'0
  have hz₁Q : c.coords (MvPolynomial.X 1) ∈ Q :=
    sncChart_coordinate_mem_point_prime c ξ σc hc j 1 hσj t' ht'c ht'j
  have hleQ : RingHom.ker (Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)})) ≤ Q := by
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact hz₀Q
  let 𝔓 : Ideal (hyperplaneTestRing c) := Q.map (Ideal.Quotient.mk _)
  haveI h𝔓 : 𝔓.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hleQ
  have hmem𝔓 : ∀ f : Γ(T, c.U), Ideal.Quotient.mk _ f ∈ 𝔓 ↔ f ∈ Q :=
    mem_map_primeIdealOf_quotient_iff c.isAffine t' ht'c _ hz₀Q
  let t'U : Spec (CommRingCat.of (hyperplaneTestRing c)) := ⟨𝔓, h𝔓⟩
  have ht'U : hyperplaneTestInclusion c t'U = t' := by
    apply specAlgebraHom_apply_of_comap c.isAffine _ t'U t' ht'c
    ext f
    exact hmem𝔓 f
  have hxH : hyperplaneTestMap c fT φ w₀ hw₀ t'U =
      specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w hw0) y := by
    apply (specFibreProductMap (Y := Y) θ).isClosedEmbedding.injective
    have h1 := congrArg (fun g : Spec (CommRingCat.of (hyperplaneTestRing c)) ⟶
      specFibreProduct K B Y => g t'U) hsq
    simp only [Scheme.Hom.comp_apply] at h1
    have h2 := congrArg (fun g : Y ⟶ specFibreProduct K B Y => g y)
      (specFibreProductFibre_comp_map θ (Ideal.Quotient.liftₐ _ w hw0))
    simp only [Scheme.Hom.comp_apply] at h2
    have hw' : (Ideal.Quotient.liftₐ _ w hw0).comp θ = w := AlgHom.ext fun b => rfl
    rw [hw'] at h2
    change (specFibreProductMap θ) (hyperplaneTestMap c fT φ w₀ hw₀ t'U) =
      (specFibreProductMap θ) (specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w hw0) y)
    rw [← h1, ht'U, hx, h2]
  -- the prime divisor e of U: a minimal prime of y_1 inside 𝔓
  haveI : NeZero (n + e) := ⟨by omega⟩
  let k₁ : Fin (n + e) := ⟨0, by omega⟩
  have hk₁ : ((k₁.succ : Fin (n + e + 1)) : Fin (n + (e + 1))) = 1 := by
    apply Fin.ext
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rfl
  let v₁ : hyperplaneTestRing c := hyperplaneCoords c.coords (MvPolynomial.X k₁)
  have hv₁ : v₁ = Ideal.Quotient.mk _ (c.coords (MvPolynomial.X 1)) := by
    change hyperplaneCoords c.coords (MvPolynomial.X k₁) = _
    rw [hyperplaneCoords_X]
    exact congrArg (fun i => Ideal.Quotient.mk _ (c.coords (MvPolynomial.X i))) hk₁
  have hv₁𝔓 : v₁ ∈ 𝔓 := by
    rw [hv₁, hmem𝔓]
    exact hz₁Q
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {v₁} ≤ 𝔓 from (Ideal.span_singleton_le_iff_mem _).mpr hv₁𝔓)
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  have hv₁𝔮 : v₁ ∈ 𝔮 := h𝔮min.1.2 (Ideal.subset_span rfl)
  have hv₁0 : v₁ ≠ 0 := by
    intro h0
    apply etaleChart_coordinate_ne_zero cU k₁
    change (Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv v₁ = 0
    rw [h0, map_zero]
  let eP : Spec (CommRingCat.of (hyperplaneTestRing c)) := ⟨𝔮, h𝔮prime⟩
  have hcoh : Order.coheight eP = 1 := by
    rw [← idealHeight_eq_coheight]
    change 𝔮.height = 1
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ 𝔮 h𝔮min
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      rintro rfl
      exact hv₁0 ((Submodule.mem_bot _).mp hv₁𝔮)
  let eC : CodimensionOnePoint (Spec (CommRingCat.of (hyperplaneTestRing c))) := ⟨eP, hcoh⟩
  haveI : Smooth (Spec (CommRingCat.of (hyperplaneTestRing c)) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth (n + e) _
  haveI : IsDiscreteValuationRing
      ((Spec (CommRingCat.of (hyperplaneTestRing c))).presheaf.stalk (eC : _)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) eC
  have hespec : eP ⤳ t'U := (PrimeSpectrum.le_iff_specializes eP t'U).mp h𝔮le
  have hcentre : specFibreProductFibre (V := Y) (Ideal.Quotient.liftₐ _ w hw0) y ∈
      closure ({hyperplaneTestMap c fT φ w₀ hw₀ (eC : _)} : Set _) := by
    rw [← hxH]
    exact (hespec.map (hyperplaneTestMap c fT φ w₀ hw₀).continuous).mem_closure
  -- 4a. the points: the generic point of U goes to ξ_{s₀}, and e goes to t ∈ c.U
  have hUc : ∀ u : Spec (CommRingCat.of (hyperplaneTestRing c)), hyperplaneTestInclusion c u ∈ c.U :=
    fun u => specAlgebraHom_top_le c.isAffine
      (Ideal.Quotient.mkₐ K (Ideal.span {c.coords (MvPolynomial.X 0)})) (Opens.mem_top u)
  have hζc := hUc (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))
  have htc := hUc (eC : Spec (CommRingCat.of (hyperplaneTestRing c)))
  have hfζ : fT (hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of
      (hyperplaneTestRing c))))) =
      specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))
        (genericPoint (specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y)) := by
    have h := congrArg (fun f : Spec (CommRingCat.of (hyperplaneTestRing c)) ⟶
      specFibreProduct K B Y => f (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))))) hsq
    simp only [Scheme.Hom.comp_apply] at h
    rw [h, hσgen]
  have hsndζ : specFibreProductSnd K B Y (fT (hyperplaneTestInclusion c
      (genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c)))))) = genericPoint Y := by
    rw [hfζ]
    change (specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
      specFibreProductSnd K B Y) _ = _
    rw [specFibreProductMap_snd]
    exact dominant_map_genericPoint _
  have hgenY : ∀ W : Y.Opens, Nonempty W → genericPoint Y ∈ W := fun W hW =>
    ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have hζP : fT (hyperplaneTestInclusion c (genericPoint (Spec (CommRingCat.of
      (hyperplaneTestRing c))))) ∈ (fibreProductEtaleChart cY φ hφ).U := by
    change specFibreProductSnd K B Y _ ∈ cY.U
    rw [hsndζ]
    exact hgenY cY.U cY.nonempty
  have hηe : genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c))) ⤳
      (eC : Spec (CommRingCat.of (hyperplaneTestRing c))) :=
    (genericPoint_spec _).specializes (Set.mem_univ _)
  have hspecT := hηe.map (hyperplaneTestInclusion c).continuous
  -- the local equation of the discrepancy divisor of fT at t and its local product
  have htV : specFibreProductSnd K B Y (fT (hyperplaneTestInclusion c
      (eC : Spec (CommRingCat.of (hyperplaneTestRing c))))) ∈ V := hcV htc
  have hδP := cartierPullback_isLocalEquationAt (specFibreProductSnd K B Y) D₀ _ (hδ _ htV)
  have hlocT := logDiscrepancyDivisor_isLocalEquationAt fT hfT (fibreProductEtaleChart cY φ hφ)
    (fibreProductPairUnit (K := K) fY) d (fibreProductPairDivisor (K := K) (B := B) D₀) cT
    (hyperplaneTestInclusion c (eC : Spec (CommRingCat.of (hyperplaneTestRing c)))) c htc hδP
  have hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z) :=
    fun z => smooth_stalk_isIntegrallyClosed (K := K) z
  haveI hDVR : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  obtain ⟨v, hv⟩ := snc_local_equation_combination hnorm c ξ hinj hξ σc hc _ _ hLsupp hHsupp _ htc
    hlocT (CartierDivisor.isLocalEquationAt_principalCartierDivisor _ tT) s₀ d
  -- the exponents: the one at s₀ vanishes
  have h01 : (0 : Fin (n + (e + 1))) ≠ 1 := by
    intro h
    have h' : ((0 : Fin (n + (e + 1))) : ℕ) = ((1 : Fin (n + (e + 1))) : ℕ) := congrArg Fin.val h
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)] at h'
    simp at h'
  have hjs : j ≠ s₀ := by
    rintro rfl
    rw [hσ₀] at hσj
    exact h01 (Option.some.inj hσj)
  let E : Fin r → ℤ := fun i => cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT
      (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover) (ξ i) -
    (d : ℤ) * cartierCoefficient (principalCartierDivisor T tT) (ξ i) + if i = s₀ then (d : ℤ) else 0
  have hE0 : E s₀ = 0 := by
    change cartierCoefficient _ (ξ s₀) - (d : ℤ) * cartierCoefficient _ (ξ s₀) +
      (if s₀ = s₀ then (d : ℤ) else 0) = 0
    rw [ite_eq_left rfl, hL₀, hh₀]
    ring
  have hEj : E j = cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT
      (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover) (ξ j) -
      (d : ℤ) * cartierCoefficient (principalCartierDivisor T tT) (ξ j) := by
    change _ - _ + (if j = s₀ then (d : ℤ) else 0) = _
    rw [ite_eq_right hjs, add_zero]
  let Mx : Fin r → ℕ := fun i => (E i).toNat
  let Nx : Fin r → ℕ := fun i => (-E i).toNat
  have hEMN : ∀ i, E i = (Mx i : ℤ) - Nx i := fun i => (Int.toNat_sub_toNat_neg (E i)).symm
  -- the component equations with the one of ξ_{s₀} removed
  let comp'' : Fin r → T.functionFieldˣ := fun i =>
    (σc i).elim 1 fun a => if a = 0 then 1 else etaleChartCoordinateRationalUnit c a
  have hprodE : (∏ i, sncChartComponentEquation c σc i ^ E i : T.functionFieldˣ) =
      ∏ i, comp'' i ^ E i := by
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases his : i = s₀
    · rw [his, hE0, zpow_zero, zpow_zero]
    · congr 1
      cases hi : σc i with
      | none => simp [sncChartComponentEquation, comp'', hi]
      | some a =>
        have ha : a ≠ 0 := fun ha => his (hc.1 i s₀ 0 (by rw [hi, ha]) hσ₀)
        simp [sncChartComponentEquation, comp'', hi, ha]
  change _ = algebraMap _ _ (Units.val v) *
    ((∏ i, sncChartComponentEquation c σc i ^ E i : T.functionFieldˣ) : T.functionField) at hv
  rw [hprodE] at hv
  have hsplit : (∏ i, comp'' i ^ E i) * (∏ i, comp'' i ^ (Nx i : ℤ)) =
      ∏ i, comp'' i ^ (Mx i : ℤ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_add, hEMN i]
    congr 1
    ring
  -- elements of the stalk of T at ζ, the generic point of ξ_{s₀}
  have hNc : Nonempty c.U := c.nonempty
  let ηU := genericPoint (Spec (CommRingCat.of (hyperplaneTestRing c)))
  let ζ₀ := hyperplaneTestInclusion c ηU
  let gT : T.presheaf.stalk ζ₀ →ₐ[K] T.functionField := stalkFunctionFieldAlgHom (K := K) ζ₀
  let gU : T.presheaf.stalk ζ₀ →ₐ[K] (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField :=
    (stalkFunctionFieldAlgHom (K := K) ηU).comp
      (schemeStalkMapAlgHom (K := K) (hyperplaneTestInclusion c) ηU)
  have hgerm : ∀ s : Γ(T, c.U), gT (T.presheaf.germ c.U ζ₀ hζc s) = T.germToFunctionField c.U s :=
    fun s => T.algebraMap_germ_eq_germToFunctionField hζc s
  have hgermU : ∀ s : Γ(T, c.U), gU (T.presheaf.germ c.U ζ₀ hζc s) =
      (Spec (CommRingCat.of (hyperplaneTestRing c))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv
          (Ideal.Quotient.mk _ s)) :=
    fun s => hyperplaneTest_residue_germ c s hζc
  obtain ⟨wS, hwS⟩ : ∃ x, x = T.presheaf.germ c.U ζ₀ hζc w₀ := ⟨_, rfl⟩
  have hwT : gT wS = T.germToFunctionField c.U w₀ := by rw [hwS]; exact hgerm w₀
  have hy0 : (sncChartComponentEquation c σc s₀ : T.functionField) =
      T.germToFunctionField c.U (c.coords (MvPolynomial.X 0)) := by
    simp only [sncChartComponentEquation, hσ₀, Option.elim_some, etaleChartCoordinateRationalUnit,
      regularEquationRationalUnit_val]
  have hTt : (tT : T.functionField) =
      (sncChartComponentEquation c σc s₀ : T.functionField) * gT wS := by
    rw [htT, map_mul, hy0, hwT]
  have hwT0 : gT wS ≠ 0 := fun h0 => tT.ne_zero (by rw [hTt, h0, mul_zero])
  obtain ⟨vS, hvS⟩ : ∃ x, x = T.presheaf.stalkSpecializes hspecT (Units.val v) :=
    ⟨_, rfl⟩
  have hvT : gT vS = algebraMap (T.presheaf.stalk _) T.functionField (Units.val v) := by
    rw [hvS]
    exact stalkFunctionFieldAlgHom_stalkSpecializes (K := K) hspecT _
  obtain ⟨WY, hWY, aY, haY⟩ := exists_unit_section_germ (fY ^ d * δ⁻¹)
  haveI := hWY
  have hζW : fT ζ₀ ∈ specFibreProductSnd K B Y ⁻¹ᵁ WY := by
    change specFibreProductSnd K B Y (fT ζ₀) ∈ WY
    rw [hsndζ]
    exact hgenY WY hWY
  obtain ⟨bS, hbS⟩ : ∃ x, x = T.presheaf.germ (fT ⁻¹ᵁ (specFibreProductSnd K B Y ⁻¹ᵁ WY)) ζ₀ hζW
      (fT.appLE _ _ le_rfl ((specFibreProductSnd K B Y).appLE WY _ le_rfl (aY : Γ(Y, WY)))) :=
    ⟨_, rfl⟩
  have hbT : gT bS = (dominantFunctionFieldMap fT).hom ((dominantFunctionFieldMap
      (specFibreProductSnd K B Y)).hom ((fY ^ d * δ⁻¹ : Y.functionFieldˣ) : Y.functionField)) := by
    rw [hbS, ← haY]
    exact hyperplaneTest_constant_value fT WY (aY : Γ(Y, WY)) ζ₀ hζW
  have hbU : gU bS = (dominantFunctionFieldMap (hyperplaneTestMap c fT φ w₀ hw₀)).hom
      ((dominantFunctionFieldMap
        (specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y)).hom
          ((fY ^ d * δ⁻¹ : Y.functionFieldˣ) : Y.functionField)) := by
    rw [hbS, ← haY]
    exact hyperplaneTest_constant_residue φ fT c w₀ hw₀ WY (aY : Γ(Y, WY)) hζW
  obtain ⟨jS, hjS⟩ : ∃ x, x = (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) fT ζ₀)
      (etaleChartStalkCoords (fibreProductEtaleChart cY φ hφ) (fT ζ₀) hζP)
      (etaleChartStalkCoords c ζ₀ hζc) (etaleChartStalkCoords_formallyEtale c ζ₀ hζc)).det :=
    ⟨_, rfl⟩
  have hjT : gT jS = chartRelativeJacobianDet fT (fibreProductEtaleChart cY φ hφ) c := by
    rw [hjS]
    exact (chartRelativeJacobianDet_eq_stalk fT ζ₀ (fibreProductEtaleChart cY φ hφ) hζP c hζc).symm
  have hjU : gU jS = ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) * gU wS *
      chartRelativeJacobianDet (hyperplaneTestMap c fT φ w₀ hw₀)
        (fibreProductEtaleChart cY (hyperplaneCoords φ) (hyperplaneCoords_formallyEtale φ hφ)) cU := by
    rw [hjS, hwS]
    exact hyperplaneTest_jacobian_residue cY φ hφ fT c w₀ hw₀ hζc hζP
  let zS : Fin r → T.presheaf.stalk ζ₀ := fun i => (σc i).elim 1 fun a =>
    if a = 0 then 1 else T.presheaf.germ c.U ζ₀ hζc (c.coords (MvPolynomial.X a))
  have hzT : ∀ i, gT (zS i) = (comp'' i : T.functionField) := by
    intro i
    cases hi : σc i with
    | none => simp [zS, comp'', hi]
    | some a =>
      by_cases ha : a = 0
      · simp [zS, comp'', hi, ha]
      · simp only [zS, comp'', hi, Option.elim_some, ite_eq_right ha,
          etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
        exact hgerm _
  let ν : Fin r → (Spec (CommRingCat.of (hyperplaneTestRing c))).functionFieldˣ := fun i =>
    (σc i).elim 1 fun a => if h : a = 0 then 1 else etaleChartCoordinateRationalUnit cU (a.pred h)
  have hzU : ∀ i, gU (zS i) = (ν i : (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) := by
    intro i
    cases hi : σc i with
    | none =>
      have h1 : zS i = 1 := by simp [zS, hi]
      have h2 : ν i = 1 := by simp [ν, hi]
      rw [h1, h2, map_one, Units.val_one]
    | some a =>
      by_cases ha : a = 0
      · have h1 : zS i = 1 := by simp [zS, hi, ha]
        have h2 : ν i = 1 := by simp [ν, hi, ha]
        rw [h1, h2, map_one, Units.val_one]
      · simp only [zS, ν, hi, Option.elim_some, ite_eq_right ha, dite_eq_right ha,
          etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
        rw [hgermU]
        change _ = (Spec (CommRingCat.of (hyperplaneTestRing c))).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv
            (hyperplaneCoords c.coords (MvPolynomial.X (a.pred ha))))
        rw [hyperplaneCoords_X, Fin.succ_pred]
        rfl
  have hprodT : ∀ m : Fin r → ℕ, ∏ i, ((comp'' i : T.functionField)) ^ m i =
      ((∏ i, comp'' i ^ (m i : ℤ) : T.functionFieldˣ) : T.functionField) := by
    intro m
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  -- the identity in the stalk of T at ζ
  have hstar : bS * jS ^ d * ∏ i, zS i ^ Nx i = vS * wS ^ d * ∏ i, zS i ^ Mx i := by
    apply IsFractionRing.injective (T.presheaf.stalk ζ₀) T.functionField
    change gT _ = gT _
    simp only [map_mul, map_pow, map_prod, hbT, hjT, hvT, hzT]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec,
      Units.val_inv_eq_inv_val, ringHom_toMonoidHom_apply, fibreProductPairUnit, map_mul,
      map_pow, map_inv₀] at hv ⊢
    rw [hTt] at hv
    rw [hprodT Nx, hprodT Mx, ← hsplit, Units.val_mul]
    have hC : (sncChartComponentEquation c σc s₀ : T.functionField) ≠ 0 := Units.ne_zero _
    have hCW : (((sncChartComponentEquation c σc s₀ : T.functionField) * gT wS) ^ d)⁻¹ *
        (sncChartComponentEquation c σc s₀ : T.functionField) ^ d * gT wS ^ d = 1 := by
      rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (pow_ne_zero _ (mul_ne_zero hC hwT0))]
    have hv2 : ∀ X : T.functionField, X * (((sncChartComponentEquation c σc s₀ : T.functionField) *
        gT wS) ^ d)⁻¹ * (sncChartComponentEquation c σc s₀ : T.functionField) ^ d =
          algebraMap (T.presheaf.stalk (hyperplaneTestInclusion c
            (eC : Spec (CommRingCat.of (hyperplaneTestRing c))))) T.functionField (Units.val v) *
            ((∏ i, comp'' i ^ E i : T.functionFieldˣ) : T.functionField) →
        X = algebraMap (T.presheaf.stalk (hyperplaneTestInclusion c
            (eC : Spec (CommRingCat.of (hyperplaneTestRing c))))) T.functionField (Units.val v) *
            ((∏ i, comp'' i ^ E i : T.functionFieldˣ) : T.functionField) * gT wS ^ d := by
      intro X hX
      calc X = X * ((((sncChartComponentEquation c σc s₀ : T.functionField) * gT wS) ^ d)⁻¹ *
            (sncChartComponentEquation c σc s₀ : T.functionField) ^ d * gT wS ^ d) := by
            rw [hCW, mul_one]
        _ = (X * (((sncChartComponentEquation c σc s₀ : T.functionField) * gT wS) ^ d)⁻¹ *
            (sncChartComponentEquation c σc s₀ : T.functionField) ^ d) * gT wS ^ d := by ring
        _ = _ := by rw [hX]
    have hv3 := hv2 _ hv
    linear_combination ((∏ i, comp'' i ^ (Nx i : ℤ) : T.functionFieldˣ) : T.functionField) * hv3
  -- its image in the function field of U
  have hstarU := congrArg gU hstar
  simp only [map_mul, map_pow, map_prod, hbU, hjU, hzU] at hstarU
  have hvU : gU vS = algebraMap ((Spec (CommRingCat.of (hyperplaneTestRing c))).presheaf.stalk
      (eC : _)) (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField
      ((hyperplaneTestInclusion c).stalkMap (eC : _) (Units.val v)) := by
    rw [hvS]
    have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply (hyperplaneTestInclusion c) ηU
      (eC : Spec (CommRingCat.of (hyperplaneTestRing c))) hηe (Units.val v)
    change stalkFunctionFieldAlgHom (K := K) ηU ((hyperplaneTestInclusion c).stalkMap ηU
      (T.presheaf.stalkSpecializes hspecT (Units.val v))) = _
    rw [h1]
    exact stalkFunctionFieldAlgHom_stalkSpecializes (K := K) hηe _
  -- the local equation of the discrepancy divisor of the test model at e
  have hσeV : specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y
      (hyperplaneTestMap c fT φ w₀ hw₀ (eC : _)) ∈ V := by
    have h := congrArg (fun f : Spec (CommRingCat.of (hyperplaneTestRing c)) ⟶ Y =>
      f (eC : Spec (CommRingCat.of (hyperplaneTestRing c)))) (hyperplaneTestMap_snd c fT φ w₀ hw₀)
    simp only [Scheme.Hom.comp_apply] at h
    rw [h]
    exact htV
  have hδH := cartierPullback_isLocalEquationAt
    (specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y) D₀ _ (hδ _ hσeV)
  have hlocU := logDiscrepancyDivisor_isLocalEquationAt (hyperplaneTestMap c fT φ w₀ hw₀) hσbij
    (fibreProductEtaleChart cY (hyperplaneCoords φ) (hyperplaneCoords_formallyEtale φ hφ))
    (fibreProductPairUnit (K := K) fY) d
    (fibreProductPairDivisor (K := K) (B := B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) D₀) cU (eC : _)
    cU trivial hδH
  have hcoefU := cartierCoefficient_eq_ord hlocU
  -- the orders along e of the components
  have hnu : ¬ IsUnit ((Spec (CommRingCat.of (hyperplaneTestRing c))).presheaf.germ cU.U (eC : _)
      trivial (cU.coords (MvPolynomial.X k₁))) := by
    change ¬ IsUnit ((Spec (CommRingCat.of (hyperplaneTestRing c))).presheaf.germ ⊤ eP trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv v₁))
    rw [spec_germ_isUnit_iff, not_not]
    exact hv₁𝔮
  have hordν : ∀ i, (Spec (CommRingCat.of (hyperplaneTestRing c))).ord
      (ν i : (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) (eC : _) =
        if i = j then 1 else 0 := by
    intro i
    cases hi : σc i with
    | none =>
      have hij : i ≠ j := fun h => by rw [h, hσj] at hi; exact Option.some_ne_none _ hi
      simp [ν, hi, hij]
    | some a =>
      by_cases ha : a = 0
      · have his : i = s₀ := hc.1 i s₀ 0 (by rw [hi, ha]) hσ₀
        have hij : i ≠ j := fun h => hjs (h.symm.trans his)
        simp [ν, hi, ha, hij]
      · simp only [ν, hi, Option.elim_some, dite_eq_right ha]
        rw [etaleChart_coordinate_ord_of_not_isUnit cU eC trivial k₁ hnu (a.pred ha)]
        by_cases hij : i = j
        · rw [ite_eq_left hij, ite_eq_left]
          rw [← hij, hi] at hσj
          have ha1 : a = 1 := Option.some.inj hσj
          apply Fin.succ_injective
          rw [Fin.succ_pred]
          exact ha1.trans hk₁.symm
        · rw [ite_eq_right hij, ite_eq_right]
          intro hk
          apply hij
          have ha1 : a = 1 := ((Fin.succ_pred a ha).symm.trans (congrArg Fin.succ hk)).trans hk₁
          exact hc.1 i j 1 (by rw [hi, ha1]) hσj
  have hprodU : ∀ m : Fin r → ℕ, ∏ i, ((ν i : (Spec (CommRingCat.of
      (hyperplaneTestRing c))).functionField)) ^ m i =
      ((∏ i, ν i ^ (m i : ℤ) : (Spec (CommRingCat.of (hyperplaneTestRing c))).functionFieldˣ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) := by
    intro m
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have hordprod : ∀ m : Fin r → ℕ, (Spec (CommRingCat.of (hyperplaneTestRing c))).ord
      (∏ i, ((ν i : (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField)) ^ m i)
        (eC : _) = m j := by
    intro m
    rw [hprodU, scheme_ord_prod_zpow]
    simp [hordν]
  have hsgn : ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) *
      ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hs0 := left_ne_zero_of_mul_eq_one hsgn
  have hords : (Spec (CommRingCat.of (hyperplaneTestRing c))).ord
      ((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
        (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) (eC : _) = 0 := by
    have h := congrArg (fun z => (Spec (CommRingCat.of (hyperplaneTestRing c))).ord z (eC : _)) hsgn
    simp only [Scheme.ord_one] at h
    rw [Scheme.ord_mul hs0 hs0] at h
    omega
  have hordv : (Spec (CommRingCat.of (hyperplaneTestRing c))).ord (gU vS) (eC : _) = 0 := by
    rw [hvU]
    have h := scheme_ord_stalk_unit (eC : Spec (CommRingCat.of (hyperplaneTestRing c)))
      (Units.map ((hyperplaneTestInclusion c).stalkMap (eC : _)).hom.toMonoidHom v)
    rw [Units.coe_map] at h
    exact h
  have hgv0 : gU vS ≠ 0 := by
    rw [hvU]
    exact ((v.isUnit.map ((hyperplaneTestInclusion c).stalkMap (eC : _)).hom).map _).ne_zero
  have hwU0 : gU wS ≠ 0 := by
    rw [hwS, hgermU]
    intro h0
    have hmk : (Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)}) w₀ :
        hyperplaneTestRing c) = 0 := by
      have h1 := Scheme.germToFunctionField_injective (Spec (CommRingCat.of (hyperplaneTestRing c)))
        ⊤ (h0.trans (map_zero _).symm)
      exact (Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).commRingCatIsoToRingEquiv.symm.injective
        (h1.trans (map_zero _).symm)
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp hmk)
    have hord1 : T.ord (etaleChartCoordinateRationalUnit c 0 : T.functionField) (ξ s₀) = 1 := by
      have h := isSNCChart_coordinate_ord c ξ hξ σc hc s₀ 0 hσ₀ ⟨ξ s₀, hξ s₀⟩ hξ₀c
      rw [ite_eq_left rfl] at h
      exact h
    have htTval : (tT : T.functionField) = (etaleChartCoordinateRationalUnit c 0 : T.functionField) *
        (etaleChartCoordinateRationalUnit c 0 : T.functionField) * T.germToFunctionField c.U q := by
      rw [htT, ← hq]
      simp only [etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val, map_mul]
      ring
    have hcoordne : (etaleChartCoordinateRationalUnit c 0 : T.functionField) ≠ 0 := Units.ne_zero _
    have hq0 : T.germToFunctionField c.U q ≠ 0 := by
      intro h
      apply tT.ne_zero
      rw [htTval, h, mul_zero]
    have hordq : 0 ≤ T.ord (T.germToFunctionField c.U q) (ξ s₀) :=
      TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg q hξ₀c
    have hcoefT := cartierCoefficient_eq_ord
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor (ξ s₀) tT)
    rw [hh₀, htTval, Scheme.ord_mul (mul_ne_zero hcoordne hcoordne) hq0,
      Scheme.ord_mul hcoordne hcoordne, hord1] at hcoefT
    omega
  -- the coefficient of the discrepancy divisor of the test model along e is L_j − d h_j
  have hcoef : cartierCoefficient (logDiscrepancyDivisor (n + e) (hyperplaneTestMap c fT φ w₀ hw₀)
      hσbij (fibreProductEtaleChart cY (hyperplaneCoords φ) (hyperplaneCoords_formallyEtale φ hφ))
      (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) D₀) cU
      etaleCharts_cover) (eC : _) = E j := by
    rw [hcoefU]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec,
      Units.val_inv_eq_inv_val, ringHom_toMonoidHom_apply, fibreProductPairUnit, map_mul,
      map_pow, map_inv₀] at hstarU ⊢
    rw [hprodU Nx, hprodU Mx] at hstarU
    have hordprod' : ∀ m : Fin r → ℕ, (Spec (CommRingCat.of (hyperplaneTestRing c))).ord
        ((∏ i, ν i ^ (m i : ℤ) : (Spec (CommRingCat.of (hyperplaneTestRing c))).functionFieldˣ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) (eC : _) = m j := by
      intro m
      rw [← hprodU]
      exact hordprod m
    have main : ∀ X : (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField,
        X * (((Equiv.Perm.sign (hyperplanePerm n e) : ℤ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) ^ d *
          ((∏ i, ν i ^ (Nx i : ℤ) : (Spec (CommRingCat.of (hyperplaneTestRing c))).functionFieldˣ) :
            (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField)) =
        gU vS * ((∏ i, ν i ^ (Mx i : ℤ) :
          (Spec (CommRingCat.of (hyperplaneTestRing c))).functionFieldˣ) :
            (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField) →
        (Spec (CommRingCat.of (hyperplaneTestRing c))).ord X (eC : _) = E j := by
      intro X hX
      have hPN0 := Units.ne_zero (∏ i, ν i ^ (Nx i : ℤ))
      have hPM0 := Units.ne_zero (∏ i, ν i ^ (Mx i : ℤ))
      have hX0 : X ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hX
        exact mul_ne_zero hgv0 hPM0 hX.symm
      have h := congrArg (fun z => (Spec (CommRingCat.of (hyperplaneTestRing c))).ord z (eC : _)) hX
      rw [Scheme.ord_mul hX0 (mul_ne_zero (pow_ne_zero _ hs0) hPN0),
        Scheme.ord_mul (pow_ne_zero _ hs0) hPN0, scheme_ord_pow hs0, hords,
        Scheme.ord_mul hgv0 hPM0, hordv, hordprod', hordprod'] at h
      rw [hEMN j]
      linarith
    apply main
    apply mul_right_cancel₀ (pow_ne_zero d hwU0)
    linear_combination hstarU
  -- 4b, 4c
  have hVV : specFibreProductSnd K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y ⁻¹ᵁ V ≤
      specFibreProductMap (Y := Y) (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ⁻¹ᵁ
        (specFibreProductSnd K B Y ⁻¹ᵁ V) := fun x hx => by
    change (specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})) ≫
      specFibreProductSnd K B Y) x ∈ V
    rw [specFibreProductMap_snd]
    exact hx
  haveI : Nonempty (hyperplaneTestInclusion c ⁻¹ᵁ c.U) := ⟨⟨_, hζc⟩⟩
  let ι' : hyperplaneTestRing c → (Spec (CommRingCat.of (hyperplaneTestRing c))).functionField :=
    fun z => (Spec (CommRingCat.of (hyperplaneTestRing c))).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv z)
  have hι'mul : ∀ a b, ι' (a * b) = ι' a * ι' b := fun a b => by
    simp only [ι', map_mul]
  have hι'pow : ∀ a (m : ℕ), ι' (a ^ m) = ι' a ^ m := fun a m => by
    simp only [ι', map_pow]
  have hι'0 : ∀ b, b ≠ 0 → ι' b ≠ 0 := by
    intro b hb h0
    apply hb
    have h1 := Scheme.germToFunctionField_injective (Spec (CommRingCat.of (hyperplaneTestRing c))) ⊤
      (h0.trans (map_zero _).symm)
    exact (Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).commRingCatIsoToRingEquiv.symm.injective
      (h1.trans (map_zero _).symm)
  have hunit' : ∀ b, b ∉ 𝔮 → (Spec (CommRingCat.of (hyperplaneTestRing c))).ord (ι' b) (eC : _) = 0 := by
    intro b hb
    have hu : IsUnit ((Spec (CommRingCat.of (hyperplaneTestRing c))).presheaf.germ ⊤ (eC : _) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv b)) :=
      (spec_germ_isUnit_iff (CommRingCat.of (hyperplaneTestRing c)) eP b).mpr hb
    have h := scheme_ord_stalk_unit (eC : Spec (CommRingCat.of (hyperplaneTestRing c))) hu.unit
    rwa [IsUnit.unit_spec, Scheme.algebraMap_germ_eq_germToFunctionField] at h
  have hreg' : ∀ b, 0 ≤ (Spec (CommRingCat.of (hyperplaneTestRing c))).ord (ι' b) (eC : _) := by
    intro b
    refine scheme_ord_nonneg_of_mem_stalk (eC : Spec (CommRingCat.of (hyperplaneTestRing c))) _
      ⟨(Spec (CommRingCat.of (hyperplaneTestRing c))).presheaf.germ ⊤ (eC : _) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (hyperplaneTestRing c))).inv b), ?_⟩
    exact Scheme.algebraMap_germ_eq_germToFunctionField _ _ _
  have hordv₁ : (Spec (CommRingCat.of (hyperplaneTestRing c))).ord (ι' v₁) (eC : _) = 1 := by
    have h := etaleChart_coordinate_ord_of_not_isUnit cU eC trivial k₁ hnu k₁
    rw [ite_eq_left rfl] at h
    exact h
  refine ⟨Spec (CommRingCat.of (hyperplaneTestRing c)), inferInstance, inferInstance,
    inferInstance, hrelU, hyperplaneTestMap c fT φ w₀ hw₀, hσdom, hσover, hσbij, cU, eC,
    hcentre, fun k hk => ?_⟩
  -- 4b. the order of the restriction of g_k along e is at least a
  obtain ⟨q, Vk, hVk, hgq⟩ := hga k
  rw [← hv₁] at hgq
  have hgk : (dominantFunctionFieldMap (hyperplaneTestMap c fT φ w₀ hw₀)).hom
      ((specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y).germToFunctionField
        (specFibreProductSnd K _ Y ⁻¹ᵁ V)
        ((specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).appLE
          (specFibreProductSnd K B Y ⁻¹ᵁ V) (specFibreProductSnd K _ Y ⁻¹ᵁ V) hVV (g k))) =
      ι' (Ideal.Quotient.mk _ (fT.appLE _ c.U hcV (g k))) := by
    rw [← residue_germ_appLE_eq_of_comm (K := K) (hyperplaneTestInclusion c) fT
      (hyperplaneTestMap c fT φ w₀ hw₀) _ hsq _ (specFibreProductSnd K B Y ⁻¹ᵁ V) c.U hcV hζc (g k)
      _ hVV]
    exact hyperplaneTest_residue_germ c _ hζc
  have hF0 : (Ideal.Quotient.mk _ (fT.appLE _ c.U hcV (g k)) : hyperplaneTestRing c) ≠ 0 := by
    intro h0
    apply hk
    apply (dominantFunctionFieldMap (hyperplaneTestMap c fT φ w₀ hw₀)).hom.injective
    rw [map_zero]
    refine hgk.trans ?_
    rw [h0]
    simp only [ι', map_zero]
  have hVk0 : Vk ≠ 0 := fun h0 => hVk (h0 ▸ Ideal.zero_mem _)
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hgq
    exact mul_ne_zero hF0 hVk0 hgq
  have hordF : (Spec (CommRingCat.of (hyperplaneTestRing c))).ord
      (ι' (Ideal.Quotient.mk _ (fT.appLE _ c.U hcV (g k)))) (eC : _) =
        a + (Spec (CommRingCat.of (hyperplaneTestRing c))).ord (ι' q) (eC : _) := by
    have h := congrArg (fun z => (Spec (CommRingCat.of (hyperplaneTestRing c))).ord (ι' z) (eC : _)) hgq
    simp only [hι'mul, hι'pow] at h
    rw [Scheme.ord_mul (hι'0 _ hF0) (hι'0 _ hVk0), Scheme.ord_mul (pow_ne_zero _ (hι'0 _ hv₁0))
      (hι'0 _ hq0), scheme_ord_pow (hι'0 _ hv₁0), hunit' Vk (fun h => hVk (h𝔮le h)), hordv₁,
      add_zero, mul_one] at h
    exact h
  -- 4c. the inequality
  change (M : ℝ) * (((d : ℝ) + (cartierCoefficient _
    (eC : Spec (CommRingCat.of (hyperplaneTestRing c))) : ℝ)) / d) ≤
    (((Spec (CommRingCat.of (hyperplaneTestRing c))).ord ((dominantFunctionFieldMap
      (hyperplaneTestMap c fT φ w₀ hw₀)).hom
      ((specFibreProduct K (B ⧸ Ideal.span {φ (MvPolynomial.X 0)}) Y).germToFunctionField
        (specFibreProductSnd K _ Y ⁻¹ᵁ V)
        ((specFibreProductMap (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))).appLE
          (specFibreProductSnd K B Y ⁻¹ᵁ V) (specFibreProductSnd K _ Y ⁻¹ᵁ V) hVV (g k))))
      (eC : _) : ℤ) : ℝ)
  rw [hcoef, hEj, hgk, hordF]
  generalize cartierCoefficient (logDiscrepancyDivisor (n + (e + 1)) fT hfT
      (fibreProductEtaleChart cY φ hφ) (fibreProductPairUnit (K := K) fY) d
      (fibreProductPairDivisor (K := K) (B := B) D₀) cT etaleCharts_cover) (ξ j) = Lj at hineq ⊢
  generalize cartierCoefficient (principalCartierDivisor T tT) (ξ j) = hj at hineq ⊢
  have hq' := hreg' q
  generalize (Spec (CommRingCat.of (hyperplaneTestRing c))).ord (ι' q) (eC : _) = oq at hq' ⊢
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((M : ℤ) * ((d : ℤ) + Lj - (d : ℤ) * hj) : ℝ) ≤ (((d : ℤ) * a : ℤ) : ℝ) := by
    exact_mod_cast hineq
  have h2 : ((a : ℤ) : ℝ) ≤ ((a + oq : ℤ) : ℝ) := by exact_mod_cast (by omega : (a : ℤ) ≤ a + oq)
  rw [mul_div_assoc', div_le_iff₀ hd0]
  push_cast at h1 h2 ⊢
  nlinarith

end Adjunction

end MixedFujita
