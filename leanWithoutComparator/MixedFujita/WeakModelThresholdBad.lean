/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltFixedIdealLemmaThree

/-!
The weak model form of lct_x ≤ 1/M, and Lemma 3 for a fixed family and an arbitrary pair
(step 15).

`ModelThresholdWeakBadAt` is `ModelThresholdBadAt` without the positivity of the log
discrepancy A(e) of the test prime. For a klt pair the two agree (check 563,
`modelThresholdBadAt_of_modelThresholdWeakBadAt_of_klt`). For an arbitrary pair the weak bad
closed points of an affine open V for finitely many sections g_j, not all zero, are the zero set
of an ideal of Γ(V) (`exists_ideal_modelThresholdWeakBadAt_of_affine`): the proof of check 564
without klt. For a weakly bad test prime the orders o_s of the members of a principalizing simple
normal crossing model along it satisfy Σ_s (d − b_s) o_s ≤ d A and M A ≤ Σ_s G_s o_s. If some
o_s is positive, some member with o_s > 0 has M (d − b_s) ≤ d G_s
(`exists_index_ge_of_weighted_sum_ge_of_exists_pos`). If all o_s vanish, the centre of the test
prime on the model lies on no member, so A is at least 1, as on the smooth model
(`exists_snc_orders_at_test_prime_sharp`), against M A ≤ 0. A bad member through the point is a
weakly bad test prime, with no positivity to check. So no klt hypothesis is needed for the
closedness, which is why the product of a klt pair with a smooth variety need not be shown klt.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section WeakBad

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The weak model form of lct_x ≤ 1/M for rational functions g_j: some prime divisor e of a
smooth birational test model, with centre containing x, has ord_e(g_j) ≥ M A(e) for every
nonzero g_j; the log discrepancy A(e) need not be positive. -/
def ModelThresholdWeakBadAt (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ : CartierDivisor Y) (x : Y) {J : Type*} (g : J → Y.functionField) (M : ℕ) : Prop :=
  ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
    (_ : U.Over (Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
    (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U),
    x ∈ closure ({σ (e : U)} : Set Y) ∧
    ∀ j, g j ≠ 0 → (M : ℝ) * (((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) ≤
      ((U.ord ((dominantFunctionFieldMap σ).hom (g j)) (e : U) : ℤ) : ℝ)

/-- A bad point is weakly bad. -/
theorem modelThresholdWeakBadAt_of_modelThresholdBadAt (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y) (x : Y) {J : Type*}
    (g : J → Y.functionField) (M : ℕ) (h : ModelThresholdBadAt cY fY d D₀ x g M) :
    ModelThresholdWeakBadAt cY fY d D₀ x g M := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, -, hg⟩ := h
  exact ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, hg⟩

/-- **For a klt pair a weakly bad point is bad**: the log discrepancy of every test prime is
positive (check 563). -/
theorem modelThresholdBadAt_of_modelThresholdWeakBadAt_of_klt [CharZero K]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d)
    (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (x : Y) {J : Type*}
    (g : J → Y.functionField) (M : ℕ) (h : ModelThresholdWeakBadAt cY fY d D₀ x g M) :
    ModelThresholdBadAt cY fY d D₀ x g M := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, hg⟩ := h
  have hpos := logPairIsKlt_testPrime_pos cY fY hd D₀ hklt σ hσ cU e
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, ?_, hg⟩
  have h0 : (0 : ℝ) < (d : ℝ) + ((cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU
      etaleCharts_cover) (e : U) : ℤ) : ℝ) := by exact_mod_cast hpos
  exact div_pos h0 hdR

end WeakBad

section TestPrime

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The orders of `exists_snc_orders_at_test_prime`, with in addition the sharp bound when no
member of the family passes through the centre: then the coefficient of the log discrepancy
divisor at x is nonnegative, that is A(x) ≥ 1, as for the smooth model with zero boundary. -/
theorem exists_snc_orders_at_test_prime_sharp {κ : Type*} [Finite κ] (c : EtaleChart K X n)
    (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (A : κ → CartierDivisor X) (hA : ∀ k, (A k).IsEffective) (G : CartierDivisor T)
    (hG : G.IsEffective)
    (hGsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient G (t : T) = 0)
    (hGI : effectiveCartierIdealSheaf G hG =
      (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap ρ)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (x : CodimensionOnePoint U) :
    ∃ (o : Fin r → ℤ) (t₀ : T), ρ t₀ = σ (x : U) ∧ (∀ s, 0 ≤ o s) ∧
      (∀ s, o s ≠ 0 → t₀ ∈ closure ({ξ s} : Set T)) ∧
      (∀ D' : CartierDivisor X, (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback ρ D') (t : T) = 0) →
        cartierCoefficient (cartierPullback σ D') (x : U) =
          ∑ s, cartierCoefficient (cartierPullback ρ D') (ξ s) * o s) ∧
      ((∀ k, ∑ s, cartierCoefficient G (ξ s) * o s ≤
          cartierCoefficient (cartierPullback σ (A k)) (x : U)) ∧
        ∃ k, ∑ s, cartierCoefficient G (ξ s) * o s =
          cartierCoefficient (cartierPullback σ (A k)) (x : U)) ∧
      (d : ℤ) * ∑ s, o s -
          ∑ s, cartierCoefficient
            (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ s) * o s ≤
        (d : ℤ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (x : U) ∧
      ((∀ s, o s = 0) → 0 ≤ cartierCoefficient
          (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (x : U)) := by
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨W, hx, hW, α, hdom, hcomm, hα⟩ :=
    proper_birational_exists_local_birational_extension ρ σ hρ hσ (x : U)
  let : Nonempty W := ⟨⟨(x : U), hx⟩⟩
  let : IsIntegral W.toScheme := hW
  let : W.toScheme.Over (Spec (CommRingCat.of K)) := ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  have : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsDominant α := hdom
  let : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  have : α.IsOver (Spec (CommRingCat.of K)) := by
    apply (Scheme.Hom.isOver_iff (Spec (CommRingCat.of K))).mpr
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := σ) (S := Spec (CommRingCat.of K)),
      HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  let w : W.toScheme := ⟨(x : U), hx⟩
  have hιbij : Function.Bijective (W.ι.stalkMap w) :=
    ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w)
  have hw : Order.coheight w = 1 :=
    (coheight_eq_of_stalkMap_bijective W.ι w hιbij).trans x.property
  let p : CodimensionOnePoint W.toScheme := ⟨w, hw⟩
  obtain ⟨cW⟩ : Nonempty (EtaleChart K W.toScheme n) :=
    ⟨Classical.choose (show ∃ e : EtaleChart K W.toScheme n, w ∈ e.U from
      TopologicalSpace.Opens.mem_iSup.mp
        ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸
          TopologicalSpace.Opens.mem_top w))⟩
  have : Smooth (W.toScheme ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hdvrW := smoothOverField_codimensionOne_stalk_DVR (K := K) p
  have hdvrU : IsDiscreteValuationRing (U.presheaf.stalk (W.ι (p : W.toScheme))) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨o, ho, hosupp, hpull, hdisc⟩ := exists_snc_orders_at_prime α hα ξ hinj hξ hsnc p
  -- coefficients on the neighbourhood are the coefficients on the test model
  have htr : ∀ D' : CartierDivisor X,
      cartierCoefficient (cartierPullback (W.ι ≫ σ) D') (p : W.toScheme) =
        cartierCoefficient (cartierPullback σ D') (x : U) := by
    intro D'
    rw [cartierPullback_comp σ W.ι D']
    exact cartierCoefficient_pullback_of_stalkMap_bijective W.ι p x.property hιbij
      (cartierPullback σ D')
  -- the coefficient at x is that of α for the crepant pair on T
  have hkey : cartierCoefficient (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover)
      (x : U) = cartierCoefficient (logDiscrepancyDivisor n α hα cT
        (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D) cW etaleCharts_cover)
        (p : W.toScheme) := by
    have heq := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
      σ W.ι hσ hι c f d D cU cW p x.property hιbij
    have hc := logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cW etaleCharts_cover
    have h2 : cartierCoefficient (logDiscrepancyDivisor n (W.ι ≫ σ)
        (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι) c f d D cW
        etaleCharts_cover) (p : W.toScheme) = cartierCoefficient (logDiscrepancyDivisor n α hα cT
        (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D) cW etaleCharts_cover)
        (p : W.toScheme) := by
      rw [← hc]
      simp only [hcomm]
    exact heq.symm.trans h2
  refine ⟨o, α w, ?_, ho, hosupp, ?_, ?_, ?_, ?_⟩
  · have h := Scheme.Hom.comp_apply α ρ w
    rw [hcomm, Scheme.Hom.comp_apply] at h
    exact h.symm
  · intro D' hD'
    have h1 := hpull (cartierPullback ρ D') hD'
    rw [← cartierPullback_comp ρ α D'] at h1
    have h2 : cartierCoefficient (cartierPullback (W.ι ≫ σ) D') (p : W.toScheme) =
        ∑ s, cartierCoefficient (cartierPullback ρ D') (ξ s) * o s := by
      simpa only [hcomm] using h1
    rw [← htr D']
    exact h2
  · have hG' := cartierPullback_isEffective α G hG
    have hI : effectiveCartierIdealSheaf (cartierPullback α G) hG' =
        (⨆ k, effectiveCartierIdealSheaf (A k) (hA k)).comap (W.ι ≫ σ) := by
      rw [effectiveCartierIdealSheaf_cartierPullback α G hG, hGI,
        ← Scheme.IdealSheafData.comap_comp, hcomm]
    have hmin := cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup
      (W.ι ≫ σ) A hA (cartierPullback α G) hG' hI (p : W.toScheme)
    rw [← hpull G hGsupp]
    simpa only [htr] using hmin
  · have h := hdisc cT (crepantPullbackFormUnit ρ hρ c f cT) d
      (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) hsupport cW
    rw [crepantBoundaryCartier_smooth_recombine,
      ← logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cW etaleCharts_cover] at h
    have h' : (d : ℤ) * ∑ s, o s -
          ∑ s, cartierCoefficient
            (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ s) * o s ≤
        (d : ℤ) + cartierCoefficient (logDiscrepancyDivisor n (W.ι ≫ σ)
          (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι)
          c f d D cW etaleCharts_cover) (p : W.toScheme) := by
      simpa only [hcomm] using h
    have heq := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
      σ W.ι hσ hι c f d D cU cW p x.property hιbij
    rw [heq] at h'
    exact h'
  · -- no member through the centre: the coefficient is d k_p ≥ 0
    intro hall
    have hrec := crepantBoundaryCartier_smooth_recombine ρ hρ c f d D cT
    have hbd : pairBoundaryCartier cT (crepantPullbackFormUnit ρ hρ c f cT) d
        (cartierPullback ρ D) = crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover := by
      unfold pairBoundaryCartier
      rw [← hrec]
      abel
    have hsplit := cartierCoefficient_logDiscrepancyDivisor_pair α hα cT
      (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D) cW (p : W.toScheme)
    rw [hbd, hpull _ hsupport] at hsplit
    have h0 := zeroBoundary_logDiscrepancy_coefficient_nonneg cT α hα cW (p : W.toScheme)
    have hz : ∑ s, cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ s) * o s = 0 :=
      Finset.sum_eq_zero fun s _ => by rw [hall s, mul_zero]
    rw [hz, sub_zero] at hsplit
    rw [hkey, hsplit]
    exact mul_nonneg (Nat.cast_nonneg d) h0

end TestPrime

section Arithmetic

/-- If Σ a_i o_i ≥ h Σ (1 + k_i) o_i with o ≥ 0 and some o_i positive, some o_i > 0 has
a_i ≥ h (1 + k_i). -/
theorem exists_index_ge_of_weighted_sum_ge_of_exists_pos {τ : Type*} [Fintype τ]
    {o a k : τ → ℤ} {h : ℤ} (ho : ∀ s, 0 ≤ o s)
    (hsum : h * ∑ s, (1 + k s) * o s ≤ ∑ s, a s * o s) (hne : ∃ s, 0 < o s) :
    ∃ s, 0 < o s ∧ h * (1 + k s) ≤ a s := by
  by_contra hno
  push Not at hno
  have hterm : ∀ s, a s * o s ≤ h * (1 + k s) * o s := by
    intro s
    rcases (ho s).lt_or_eq with hs | hs
    · exact mul_le_mul_of_nonneg_right (hno s hs).le (ho s)
    · rw [← hs, mul_zero, mul_zero]
  obtain ⟨s₀, hs₀⟩ := hne
  have hlt : ∑ s, a s * o s < ∑ s, h * (1 + k s) * o s :=
    Finset.sum_lt_sum (fun s _ => hterm s)
      ⟨s₀, Finset.mem_univ _, mul_lt_mul_of_pos_right (hno s₀ hs₀) hs₀⟩
  have heq : ∑ s, h * (1 + k s) * o s = h * ∑ s, (1 + k s) * o s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

end Arithmetic

section FixedIdeal

variable {K : Type u} [Field K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  {n : ℕ}

omit [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))] in
/-- **Lemma 3 for a fixed family in the weak model form, for an arbitrary pair**: the closed
points of an affine open V at which the threshold of the sections g_j (not all zero) is at most
1/M in the weak model form are the zero set of an ideal of Γ(V). No klt or effectivity
hypothesis on the pair is made. -/
theorem exists_ideal_modelThresholdWeakBadAt_of_affine (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] {J : Type}
    [Finite J] (g : J → Γ(Y, V)) (hg : ∃ j, Y.germToFunctionField V (g j) ≠ 0) (M : ℕ)
    (hM : 1 ≤ M) :
    ∃ I : Ideal Γ(Y, V), ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) →
      (ModelThresholdWeakBadAt cY fY d D₀ y (fun j => Y.germToFunctionField V (g j)) M ↔
        ∀ h ∈ I, h ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  set gY : J → Y.functionField := fun j => Y.germToFunctionField V (g j) with hgY
  -- the nonzero members and their divisors
  let J' := {j : J // gY j ≠ 0}
  have : Nonempty J' := by
    obtain ⟨j, hj⟩ := hg
    exact ⟨⟨j, hj⟩⟩
  -- V as a scheme over K
  have : IsAffine V.toScheme := hV
  let : V.toScheme.Over (Spec (CommRingCat.of K)) := ⟨V.ι ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  have : V.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := V.ι) (S := Spec (CommRingCat.of K))]
    infer_instance
  have : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of K)) := inferInstance
  have : IsSeparated (V.toScheme ↘ Spec (CommRingCat.of K)) := inferInstance
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) V.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion V.ι
  obtain ⟨cX⟩ : Nonempty (EtaleChart K V.toScheme n) :=
    exists_etaleChart_on_integral_open_immersion V.ι cY
  set fX : V.toScheme.functionFieldˣ := crepantPullbackFormUnit V.ι hι cY fY cX with hfX
  set DX : CartierDivisor V.toScheme := cartierPullback V.ι D₀ with hDX
  let uY : J' → Y.functionFieldˣ := fun j => Units.mk0 (gY j.1) j.2
  let A : J' → CartierDivisor V.toScheme := fun j =>
    cartierPullback V.ι (principalCartierDivisor Y (uY j))
  have hA : ∀ j, (A j).IsEffective := by
    intro j
    have : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
    change (cartierPullback V.ι (principalCartierDivisor Y (uY j))).IsEffective
    rw [cartierPullback_principal, CartierDivisor.isEffective_principalCartierDivisor_iff]
    refine ⟨V.ι.appLE V ⊤ V.ι_preimage_self.ge (g j.1), ?_⟩
    rw [Units.coe_map]
    exact (dominantFunctionFieldMap_germ V.ι V ⊤ V.ι_preimage_self.ge (g j.1)).symm
  -- a principalizing simple normal crossing model of V
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, -, -, -, -, -, Gc, hGc, hGcI, hGc0, hmin, -⟩ :=
    exists_projective_snc_model_principalizing_sum (n := n) cX fX d DX
      (Empty.elim : Empty → CartierDivisor V.toScheme) A hA
      (Empty.elim : Empty → V.toScheme.IdealSheafData) (fun j => j.elim)
  set crep : Fin r → ℤ := fun s =>
    cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover) (ξ s)
    with hcrep
  set G : Fin r → ℤ := fun s => cartierCoefficient Gc (ξ s) with hG
  set bad : Set (Fin r) := {s | (M : ℤ) * ((d : ℤ) - crep s) ≤ (d : ℤ) * G s} with hbad
  set Z : Set V.toScheme := ⋃ s ∈ bad, ρ '' closure ({ξ s} : Set T) with hZdef
  have hZ : IsClosed Z := (Set.toFinite bad).isClosed_biUnion fun s _ =>
    (Scheme.Hom.isClosedMap ρ) _ isClosed_closure
  -- the vanishing ideal of the bad set
  have hZiff : ∀ w : V.toScheme, w ∈ Z ↔
      ∀ h ∈ (⨅ (z : V.toScheme) (_ : z ∈ Z), (hV.primeIdealOf z).asIdeal),
        h ∈ (hV.primeIdealOf w).asIdeal := by
    intro w
    constructor
    · intro hw h hh
      exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hh w) hw
    · intro hw
      by_contra hwZ
      let W : Y.Opens := ⟨V.ι '' Zᶜ, V.ι.isOpenEmbedding.isOpenMap _ hZ.isOpen_compl⟩
      obtain ⟨f, hfle, hwf⟩ := hV.exists_basicOpen_le (V := W) ⟨V.ι w, ⟨w, hwZ, rfl⟩⟩ w.2
      have hf : f ∈ (⨅ (z : V.toScheme) (_ : z ∈ Z), (hV.primeIdealOf z).asIdeal) := by
        refine (Submodule.mem_iInf _).mpr fun z => (Submodule.mem_iInf _).mpr fun hz => ?_
        by_contra hfz
        have hzf : z.1 ∈ Y.basicOpen f :=
          (mem_basicOpen_iff_notMem_primeIdealOf hV z.1 z.2 f).mpr hfz
        obtain ⟨z', hz'Z, hz'⟩ := hfle hzf
        have : z' = z := V.ι.isOpenEmbedding.injective hz'
        exact hz'Z (this ▸ hz)
      exact (mem_basicOpen_iff_notMem_primeIdealOf hV w.1 w.2 f).mp hwf (hw f hf)
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨⨅ (z : V.toScheme) (_ : z ∈ Z), (hV.primeIdealOf z).asIdeal, fun y hy _ => ?_⟩
  rw [← hZiff ⟨y, hy⟩]
  constructor
  · -- a weakly bad test prime forces a bad member of the family through its centre
    rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hye, hineq⟩
    set logY : ℤ := cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU
      etaleCharts_cover) (e : U) with hlogY
    have heV : σ (e : U) ∈ V := (specializes_iff_mem_closure.mpr hye).mem_open V.isOpen hy
    let U' : U.Opens := σ ⁻¹ᵁ V
    have : Nonempty U' := ⟨⟨(e : U), heV⟩⟩
    let : U'.toScheme.Over (Spec (CommRingCat.of K)) := ⟨U'.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
    have : U'.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    have : IsDominant U'.ι :=
      ⟨U'.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    have : SmoothOfRelativeDimension n (U'.toScheme ↘ Spec (CommRingCat.of K)) := by
      rw [← HomIsOver.comp_over (f := U'.ι) (S := Spec (CommRingCat.of K))]
      have h : SmoothOfRelativeDimension (0 + n) (U'.ι ≫ (U ↘ Spec (CommRingCat.of K))) :=
        inferInstance
      simpa only [Nat.zero_add] using h
    have : IsDominant (σ ∣_ V) := isDominant_morphismRestrict_integral σ V
    have hsq : (σ ∣_ V) ≫ V.ι = U'.ι ≫ σ := morphismRestrict_ι σ V
    have : (σ ∣_ V).IsOver (Spec (CommRingCat.of K)) := by
      constructor
      change (σ ∣_ V) ≫ V.ι ≫ (Y ↘ Spec (CommRingCat.of K)) =
        U'.ι ≫ (U ↘ Spec (CommRingCat.of K))
      rw [← Category.assoc, hsq, Category.assoc, HomIsOver.comp_over]
    have hU'ι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) U'.ι) :=
      dominantFunctionFieldMap_bijective_of_isOpenImmersion U'.ι
    have hσ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (σ ∣_ V)) := by
      have h2 := dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι
      rw [← dominantFunctionFieldAlgHom_congr_hom hsq, dominantFunctionFieldAlgHom_comp,
        AlgHom.coe_comp] at h2
      exact (Function.Bijective.of_comp_iff _ hι).mp h2
    have hbij : Function.Bijective (U'.ι.stalkMap ⟨(e : U), heV⟩) :=
      ConcreteCategory.bijective_of_isIso _
    let e' : CodimensionOnePoint U'.toScheme :=
      ⟨⟨(e : U), heV⟩,
        (coheight_eq_of_stalkMap_bijective U'.ι ⟨(e : U), heV⟩ hbij).trans e.property⟩
    obtain ⟨cU'⟩ : Nonempty (EtaleChart K U'.toScheme n) := by
      obtain ⟨c, -⟩ := Opens.mem_iSup.mp
        ((etaleCharts_cover (K := K) (X := U'.toScheme) (n := n)).symm ▸
          Opens.mem_top (e' : U'.toScheme))
      exact ⟨c⟩
    obtain ⟨o, t₀, ht₀, ho, hosupp, -, ⟨-, j₀, hj₀⟩, hdisc, hzero⟩ :=
      exists_snc_orders_at_test_prime_sharp ρ hρ cX fX d DX cT ξ hinj hcoh hsnc hsupp A hA Gc
        hGc hGc0 hGcI (σ ∣_ V) hσ' cU' e'
    -- orders and discrepancies on the part of the test model over V
    have hord : ∀ k : J', cartierCoefficient (cartierPullback (σ ∣_ V) (A k))
        (e' : U'.toScheme) = U.ord ((dominantFunctionFieldMap σ).hom (gY k.1)) (e : U) := by
      intro k
      have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
      have : Smooth (U'.toScheme ↘ Spec (CommRingCat.of K)) :=
        SmoothOfRelativeDimension.smooth n _
      have := smoothOverField_codimensionOne_stalk_DVR (K := K)
        (⟨U'.ι (e' : U'.toScheme), e.property⟩ : CodimensionOnePoint U)
      have := smoothOverField_codimensionOne_stalk_DVR (K := K) e'
      change cartierCoefficient (cartierPullback (σ ∣_ V)
        (cartierPullback V.ι (principalCartierDivisor Y (uY k)))) _ = _
      rw [← cartierPullback_comp V.ι (σ ∣_ V), cartierPullback_congr_hom hsq,
        cartierPullback_comp σ U'.ι,
        cartierCoefficient_pullback_of_stalkMap_bijective U'.ι e' e.property hbij,
        cartierPullback_principal, cartierCoefficient_principal]
      rfl
    have hlog : cartierCoefficient (logDiscrepancyDivisor n (σ ∣_ V) hσ' cX fX d DX cU'
        etaleCharts_cover) (e' : U'.toScheme) = logY := by
      rw [hfX, hDX, ← logDiscrepancyDivisor_comp V.ι (σ ∣_ V) hι hσ' cY fY d D₀ cX cU'
        etaleCharts_cover, logDiscrepancyDivisor_congr_hom hsq _
        (dominantFunctionFieldAlgHom_comp_bijective σ U'.ι hσ hU'ι)]
      exact logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ U'.ι hσ hU'ι cY fY d
        D₀ cU cU' e' e.property hbij
    -- the weighted inequality
    have hb := hineq j₀.1 j₀.2
    rw [← hord j₀, ← hj₀] at hb
    have hbZ : (M : ℤ) * ((d : ℤ) + logY) ≤ (d : ℤ) * ∑ s, G s * o s := by
      have hb' : (M : ℝ) * (((d : ℝ) + (logY : ℝ)) / d) ≤ ((∑ s, G s * o s : ℤ) : ℝ) := hb
      have h1 : (M : ℝ) * (((d : ℝ) + (logY : ℝ)) / d) * d = (M : ℝ) * ((d : ℝ) + (logY : ℝ)) := by
        field_simp
      have h2 : (M : ℝ) * ((d : ℝ) + (logY : ℝ)) ≤ (d : ℝ) * ((∑ s, G s * o s : ℤ) : ℝ) := by
        rw [← h1]
        nlinarith
      exact_mod_cast h2
    rw [hlog] at hdisc hzero
    have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
    by_cases hall : ∀ s, o s = 0
    · -- no member through the centre: A ≥ 1 against M A ≤ 0
      exfalso
      have hlog0 := hzero hall
      have hG0 : ∑ s, G s * o s = 0 := Finset.sum_eq_zero fun s _ => by rw [hall s, mul_zero]
      rw [hG0, mul_zero] at hbZ
      nlinarith
    push Not at hall
    obtain ⟨s₀, hs₀⟩ := hall
    have hsum : (M : ℤ) * ∑ s, (1 + ((d : ℤ) - 1 - crep s)) * o s ≤
        ∑ s, ((d : ℤ) * G s) * o s := by
      have h1 : ∑ s, (1 + ((d : ℤ) - 1 - crep s)) * o s =
          (d : ℤ) * ∑ s, o s - ∑ s, crep s * o s := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      have h2 : ∑ s, ((d : ℤ) * G s) * o s = (d : ℤ) * ∑ s, G s * o s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h1, h2]
      have hM0 : (0 : ℤ) ≤ M := by positivity
      exact (mul_le_mul_of_nonneg_left hdisc hM0).trans hbZ
    obtain ⟨s, hos, hs⟩ := exists_index_ge_of_weighted_sum_ge_of_exists_pos ho hsum
      ⟨s₀, lt_of_le_of_ne (ho s₀) (Ne.symm hs₀)⟩
    have hsbad : s ∈ bad := by
      change (M : ℤ) * ((d : ℤ) - crep s) ≤ (d : ℤ) * G s
      linarith [hs]
    -- the centre of e lies in the image of the closure of the bad member
    have hyc : (⟨y, hy⟩ : V.toScheme) ∈
        closure ({(σ ∣_ V) (e' : U'.toScheme)} : Set V.toScheme) := by
      have h1 : V.ι ((σ ∣_ V) (e' : U'.toScheme)) = σ (e : U) := by
        rw [← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply]
        rfl
      apply (mem_closure_singleton_open_immersion_iff V.ι ((σ ∣_ V) (e' : U'.toScheme))
        ⟨y, hy⟩).mp
      rw [h1]
      exact hye
    rw [← ht₀] at hyc
    exact Set.mem_biUnion hsbad (closure_minimal
      (Set.singleton_subset_iff.mpr (Set.mem_image_of_mem ρ (hosupp s hos.ne')))
      ((Scheme.Hom.isClosedMap ρ) _ isClosed_closure) hyc)
  · -- a bad member through the point is a weakly bad test prime of Y
    intro hw
    obtain ⟨s, hs, t, ht, hty⟩ := Set.mem_iUnion₂.mp hw
    have hσT := dominantFunctionFieldAlgHom_comp_bijective V.ι ρ hι hρ
    have hcomp : logDiscrepancyDivisor n (ρ ≫ V.ι) hσT cY fY d D₀ cT etaleCharts_cover =
        logDiscrepancyDivisor n ρ hρ cX fX d DX cT etaleCharts_cover :=
      logDiscrepancyDivisor_comp V.ι ρ hι hρ cY fY d D₀ cX cT etaleCharts_cover
    have hc : crep s = - cartierCoefficient (logDiscrepancyDivisor n ρ hρ cX fX d DX cT
        etaleCharts_cover) (ξ s) := by
      change cartierCoefficient (crepantBoundaryCartier ρ hρ cX fX d DX cT etaleCharts_cover)
        (ξ s) = _
      rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
    have hcoef : cartierCoefficient (logDiscrepancyDivisor n (ρ ≫ V.ι) hσT cY fY d D₀ cT
        etaleCharts_cover) (ξ s) = - crep s := by
      rw [hcomp]
      linarith [hc]
    refine ⟨T, hTi, inferInstance, hTo, hTs, ρ ≫ V.ι, inferInstance, inferInstance, hσT, cT,
      ⟨ξ s, hcoh s⟩, ?_, ?_⟩
    · have h1 : ρ t ∈ closure ({ρ (ξ s)} : Set V.toScheme) :=
        map_mem_closure ρ.continuous ht fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          rfl
      have h2 := (mem_closure_singleton_open_immersion_iff V.ι (ρ (ξ s)) (ρ t)).mpr h1
      rw [hty] at h2
      rw [Scheme.Hom.comp_apply]
      exact h2
    · intro j hj
      have hordT : T.ord ((dominantFunctionFieldMap (ρ ≫ V.ι)).hom (gY j)) (ξ s) =
          cartierCoefficient (cartierPullback ρ (A ⟨j, hj⟩)) (ξ s) := by
        change _ = cartierCoefficient (cartierPullback ρ
          (cartierPullback V.ι (principalCartierDivisor Y (uY ⟨j, hj⟩)))) (ξ s)
        rw [← cartierPullback_comp V.ι ρ, cartierPullback_principal, cartierCoefficient_principal]
        rfl
      have hmin1 := (hmin (ξ s)).1 ⟨j, hj⟩
      have hsZ : (M : ℤ) * ((d : ℤ) - crep s) ≤ (d : ℤ) * G s := hs
      have hG1 : G s ≤ cartierCoefficient (cartierPullback ρ (A ⟨j, hj⟩)) (ξ s) := hmin1
      rw [hcoef, ← hordT] at *
      have hfinZ : (M : ℤ) * ((d : ℤ) - crep s) ≤
          (d : ℤ) * T.ord ((dominantFunctionFieldMap (ρ ≫ V.ι)).hom (gY j)) (ξ s) := by
        nlinarith
      have hfinR : (M : ℝ) * ((d : ℝ) - (crep s : ℝ)) ≤
          (d : ℝ) * ((T.ord ((dominantFunctionFieldMap (ρ ≫ V.ι)).hom (gY j)) (ξ s) : ℤ) : ℝ) := by
        exact_mod_cast hfinZ
      have key : (M : ℝ) * (((d : ℝ) + ((-crep s : ℤ) : ℝ)) / d) =
          ((M : ℝ) * ((d : ℝ) - (crep s : ℝ))) / d := by
        push_cast
        ring
      rw [key, div_le_iff₀ hdR]
      linarith

end FixedIdeal

end MixedFujita
