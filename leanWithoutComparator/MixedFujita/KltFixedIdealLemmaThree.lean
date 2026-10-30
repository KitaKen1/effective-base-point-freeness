/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltTestPrimePositivity
public import MixedFujita.FixedIdealLemmaThree
public import MixedFujita.EtaleChartOpenRestriction

/-!
Lemma 3 for a fixed family and a klt pair on an arbitrary variety (step 15).

The klt version of check 307: on an affine open V of an integral variety of finite type over an
field of characteristic zero, for a klt pair (c_Y, f_Y, d, D₀) and finitely
many sections g_j of V, not all zero, the closed points of V at which the threshold of the g_j is
at most 1/M in the model form are the zero set of an ideal of Γ(V)
(`exists_ideal_modelThresholdBadAt_of_affine_klt`). No smoothness is assumed.

The pair is transported to V (with the crepant form of the open immersion and a chart of V from a
chart of Y, check 291), and a projective simple normal crossing model T of V principalizes the
sum of the ideal sheaves of the divisors of the g_j. A member ξ_s with crepant coefficient b_s
and coefficient G_s of the principalized divisor is bad if M (d − b_s) ≤ d G_s. For a bad test
prime of Y through y the orders o_s along it satisfy d Σ_s o_s − Σ_s b_s o_s ≤ d A and
Σ_s G_s o_s = min_j ord g_j (check 307), so some bad member with o_s > 0 passes through y. A bad
member is a test prime of Y with positive log discrepancy (check 563). So the bad closed points
are those of the image of the closures of the bad members, a closed set by properness.
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

section FixedIdeal

variable {K : Type u} [Field K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  {n : ℕ}

/-- **Lemma 3 for a fixed family and a klt pair on an affine open of an arbitrary variety**: the
closed points of V at which the threshold of the sections g_j (not all zero) is at most 1/M in
the model form are the zero set of an ideal of Γ(V). -/
theorem exists_ideal_modelThresholdBadAt_of_affine_klt (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] {J : Type}
    [Finite J] (g : J → Γ(Y, V)) (hg : ∃ j, Y.germToFunctionField V (g j) ≠ 0) (M : ℕ)
    (hM : 1 ≤ M) :
    ∃ I : Ideal Γ(Y, V), ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) →
      (ModelThresholdBadAt cY fY d D₀ y (fun j => Y.germToFunctionField V (g j)) M ↔
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
  · -- a bad test prime forces a bad member of the family through its centre
    rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hye, hApos, hineq⟩
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
    obtain ⟨o, t₀, ht₀, ho, hosupp, -, ⟨-, j₀, hj₀⟩, hdisc⟩ :=
      exists_snc_orders_at_test_prime ρ hρ cX fX d DX cT ξ hinj hcoh hsnc hsupp A hA Gc hGc hGc0
        hGcI (σ ∣_ V) hσ' cU' e'
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
    have hAZ : 0 < (d : ℤ) + logY := by
      have : (0 : ℝ) < ((d : ℝ) + (logY : ℝ)) / d := hApos
      have h2 : (0 : ℝ) < (d : ℝ) + (logY : ℝ) := by
        by_contra hneg
        push Not at hneg
        have : ((d : ℝ) + (logY : ℝ)) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hdR.le
        linarith
      exact_mod_cast h2
    rw [hlog] at hdisc
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
    have hpos : 0 < ∑ s, ((d : ℤ) * G s) * o s := by
      have h2 : ∑ s, ((d : ℤ) * G s) * o s = (d : ℤ) * ∑ s, G s * o s := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h2]
      have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hM
      nlinarith
    obtain ⟨s, hos, hs⟩ := exists_index_ge_of_weighted_sum_ge ho hsum hpos
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
  · -- a bad member through the point is a bad test prime of Y
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
    have hposT := logPairIsKlt_testPrime_pos cY fY hd D₀ hklt (ρ ≫ V.ι) hσT cT ⟨ξ s, hcoh s⟩
    refine ⟨T, hTi, inferInstance, hTo, hTs, ρ ≫ V.ι, inferInstance, inferInstance, hσT, cT,
      ⟨ξ s, hcoh s⟩, ?_, ?_, ?_⟩
    · have h1 : ρ t ∈ closure ({ρ (ξ s)} : Set V.toScheme) :=
        map_mem_closure ρ.continuous ht fun x hx => by
          rw [Set.mem_singleton_iff.mp hx]
          rfl
      have h2 := (mem_closure_singleton_open_immersion_iff V.ι (ρ (ξ s)) (ρ t)).mpr h1
      rw [hty] at h2
      rw [Scheme.Hom.comp_apply]
      exact h2
    · have h0' : (0 : ℝ) < (d : ℝ) + ((cartierCoefficient (logDiscrepancyDivisor n (ρ ≫ V.ι)
          hσT cY fY d D₀ cT etaleCharts_cover) (ξ s) : ℤ) : ℝ) := by exact_mod_cast hposT
      exact div_pos h0' hdR
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
