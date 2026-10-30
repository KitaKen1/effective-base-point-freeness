/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothPairBoundaryAbsorption
public import MixedFujita.IsolationExtractionPrime
public import MixedFujita.SNCModelPrimeOrders
public import MixedFujita.CrepantDiscrepancyComposition
public import MixedFujita.DiscrepancyPrimeComparison
public import MixedFujita.FixedIdealLemmaThree
public import MixedFujita.BirationalLocalExtension

/-!
Positivity of the log discrepancies of a klt pair along every prime of every smooth birational
test model, on an arbitrary integral variety (step 15).

The pair is klt when its discrepancies are > -1 along the prime divisors of every proper smooth
birational model; a test model need not be proper. Let ρ : T → Y be a projective simple normal
crossing model whose crepant boundary B is supported on the members ξ_s (coefficients b_s < d by
klt), and α : W → T the extension of a test model near a prime p (valuative criterion). On the
smooth T the discrepancy divisor of α for the crepant pair is d K_{W/T} − α*B
(`logDiscrepancyDivisor_pair_eq`, check 560), whose coefficient at p is d k_p − Σ_s b_s o_s with
k_p ≥ 0 and o_s the orders of the members along p. If some o_s is positive, the bound
d Σ_s o_s − Σ_s b_s o_s ≤ d + coefficient (check 307) is positive; otherwise the coefficient is
d k_p ≥ 0. Either way d A(p) = d + coefficient > 0 (`logPairIsKlt_testPrime_pos`).
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
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Positivity

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- **A klt pair has positive log discrepancy along every prime of every smooth birational test
model**, on an arbitrary integral variety of finite type over a field of characteristic zero. -/
theorem logPairIsKlt_testPrime_pos (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ)) (cU : EtaleChart K U n)
    (x : CodimensionOnePoint U) :
    0 < (d : ℤ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (x : U) := by
  classical
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, -, hρ, cT, r, ξ, hinj, hcoh, hsnc,
    hsupp, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    exists_projective_snc_model_principalizing_sum (X := Y) cY fY d D₀
      (Empty.elim : Empty → CartierDivisor Y) (fun _ : Unit => (0 : CartierDivisor Y))
      (fun _ => CartierDivisor.isEffective_zero) (Empty.elim : Empty → Y.IdealSheafData)
      (fun j => j.elim)
  -- the crepant coefficients are < d by klt
  have hb : ∀ s, cartierCoefficient
      (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s) < d := by
    intro s
    have h1 := hklt T ρ hρ cT (ξ s) (hcoh s)
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
    linarith
  -- the extension of the test model near x
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨W, hx, hW, α, hdomα, hcomm, hα⟩ :=
    proper_birational_exists_local_birational_extension ρ σ hρ hσ (x : U)
  let : Nonempty W := ⟨⟨(x : U), hx⟩⟩
  let : IsIntegral W.toScheme := hW
  let : W.toScheme.Over (Spec (CommRingCat.of K)) := ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  have : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsDominant α := hdomα
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
  obtain ⟨o, ho, -, hpull, hdisc⟩ := exists_snc_orders_at_prime α hα ξ hinj hcoh hsnc p
  -- the coefficient at x is the coefficient of α for the crepant pair on T
  have hkey : cartierCoefficient (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover)
      (x : U) = cartierCoefficient (logDiscrepancyDivisor n α hα cT
        (crepantPullbackFormUnit ρ hρ cY fY cT) d (cartierPullback ρ D₀) cW etaleCharts_cover)
        (p : W.toScheme) := by
    have heq := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
      σ W.ι hσ hι cY fY d D₀ cU cW p x.property hιbij
    have hc := logDiscrepancyDivisor_comp ρ α hρ hα cY fY d D₀ cT cW etaleCharts_cover
    have h2 : cartierCoefficient (logDiscrepancyDivisor n (W.ι ≫ σ)
        (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι) cY fY d D₀ cW
        etaleCharts_cover) (p : W.toScheme) = cartierCoefficient (logDiscrepancyDivisor n α hα cT
        (crepantPullbackFormUnit ρ hρ cY fY cT) d (cartierPullback ρ D₀) cW etaleCharts_cover)
        (p : W.toScheme) := by
      rw [← hc]
      simp only [hcomm]
    exact heq.symm.trans h2
  -- the boundary of the crepant pair on T is the crepant boundary
  have hrec := crepantBoundaryCartier_smooth_recombine ρ hρ cY fY d D₀ cT
  have hbd : pairBoundaryCartier cT (crepantPullbackFormUnit ρ hρ cY fY cT) d
      (cartierPullback ρ D₀) = crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover := by
    unfold pairBoundaryCartier
    rw [← hrec]
    abel
  by_cases hall : ∀ s, o s = 0
  · -- no member through the centre: the coefficient is d k_p ≥ 0
    have hsplit := cartierCoefficient_logDiscrepancyDivisor_pair α hα cT
      (crepantPullbackFormUnit ρ hρ cY fY cT) d (cartierPullback ρ D₀) cW (p : W.toScheme)
    rw [hbd, hpull _ hsupp] at hsplit
    have h0 := zeroBoundary_logDiscrepancy_coefficient_nonneg cT α hα cW (p : W.toScheme)
    have hz : ∑ s, cartierCoefficient
        (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s) * o s = 0 :=
      Finset.sum_eq_zero fun s _ => by rw [hall s, mul_zero]
    rw [hz, sub_zero] at hsplit
    have hd' : (0 : ℤ) < d := by exact_mod_cast hd
    nlinarith [hkey, hsplit, h0, hd']
  · -- a member through the centre: the bound of check 307 is positive by klt
    push Not at hall
    obtain ⟨s₀, hs₀⟩ := hall
    have h1 := hdisc cT (crepantPullbackFormUnit ρ hρ cY fY cT) d
      (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) hsupp cW
    rw [hrec] at h1
    have hpos : 0 < ∑ s, ((d : ℤ) - cartierCoefficient
        (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s)) * o s := by
      apply Finset.sum_pos' (fun s _ => mul_nonneg (by linarith [hb s]) (ho s))
      exact ⟨s₀, Finset.mem_univ _,
        mul_pos (by linarith [hb s₀]) (lt_of_le_of_ne (ho s₀) (Ne.symm hs₀))⟩
    have hsum : ∑ s, ((d : ℤ) - cartierCoefficient
        (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s)) * o s =
        (d : ℤ) * ∑ s, o s - ∑ s, cartierCoefficient
          (crepantBoundaryCartier ρ hρ cY fY d D₀ cT etaleCharts_cover) (ξ s) * o s := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    linarith [hkey, h1, hpos, hsum]

end Positivity

end MixedFujita
