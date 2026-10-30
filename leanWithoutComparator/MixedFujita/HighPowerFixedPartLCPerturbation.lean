/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FixedPartThresholdArithmetic
public import MixedFujita.CartierFixedPartSectionDescent
public import MixedFujita.CartierGloballyGeneratedBoundaryPerturbation
public import MixedFujita.NormalEffectiveCartierPrime
public import MixedFujita.IsolationRationalData
public import MixedFujita.CrepantBertiniPerturbationDescent
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.CrepantSNCBasePointLogCanonical
public import MixedFujita.CrepantSNCBasePointKlt

/-! 高倍数の一つの実Bertini切断から固定中心外kltとなるlc非klt摂動。 See reports/check-248-high-power-lc-perturbation-complete-base.json for the verified scope. One high residual-power Bertini cut constructs an original effective lc non-klt perturbation klt outside the complete base locus, from one initial nonzero section and a nonempty base. SNC principalization, nonzero fixed part, residual generation, threshold, power and original section descent are internal. A nonempty reduced lower-dimensional non-klt W is internally placed inside that complete base locus without KV. Initial and restricted-section nonvanishing, automatic perturbed adjoint nef-big conditions, usual KV, klt BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra




/-- A SINGLE Bertini cut of a high residual multiple constructs an ORIGINAL lc
non-klt perturbation which is klt outside the prescribed fixed-part centres.
The positive rational threshold and N=a+1 are chosen BEFORE the cut; no endpoint,
perturbing original section, or klt-away-from-Z conclusion is supplied. -/
theorem exists_lc_nonKlt_high_power_perturbation_klt_outside_fixed_centers
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p] [p.IsOver (Spec (CommRingCat.of K))]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover) (t : T) = 0)
    (M : CartierDivisor X) (F : CartierDivisor T) (hF : F.IsEffective) (hFne : F ≠ 0)
    (hFsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient F (t : T) = 0)
    (hfree : CartierIsGloballyGenerated (cartierPullback p M - F))
    (Z : Closeds X) (hcenters : ∀ t : CodimensionOnePoint T,
      0 < cartierCoefficient F (t : T) → p (t : T) ∈ Z) :
    ∃ (a q N : ℕ), 1 ≤ a ∧ 1 ≤ q ∧ N = a + 1 ∧ a < q * N ∧
      ∃ (t : Γ((N • M).sheaf, ⊤)) (ht : t ≠ 0),
        LogPairBoundaryEffective cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) ∧
        LogPairIsLogCanonical cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) ∧
        (¬ LogPairIsKlt cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht)) ∧
        ∀ x : X, x ∉ Z → LogPairIsKltOverBasePoint (𝟙 X) x cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) := by
  classical
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let B := crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover
  have hb (t : CodimensionOnePoint T) : cartierCoefficient B (t : T) < (d : ℤ) :=
    logPairIsKlt_crepantBoundary_coefficient_lt p hp cX fX d D hklt cT t
  have hg (t : CodimensionOnePoint T) : 0 ≤ cartierCoefficient F (t : T) :=
    cartierCoefficient_nonneg_of_isEffective F hF (t : T)
  obtain ⟨t₀, ht₀⟩ := exists_positive_prime_coefficient_of_effective_ne_zero hnormT F hF hFne
  have hin : (t₀ : T) ∈ Set.range ξ := by
    by_contra h
    rw [hFsupp t₀ h] at ht₀
    omega
  obtain ⟨i₀, hi₀⟩ := hin
  have hpos : ∃ i, 0 < cartierCoefficient F (ξ i) := ⟨i₀, by simpa only [hi₀] using ht₀⟩
  obtain ⟨a, q, ha, hq, hsmall, hupper, ⟨i, hgi, heq⟩, hcritical⟩ :=
    finite_integer_fixed_part_threshold_with_subcritical_moving_power
      (fun i => cartierCoefficient B (ξ i)) (fun i => cartierCoefficient F (ξ i)) d hd
      (fun i => hb ⟨ξ i, hξ i⟩) (fun i => hg ⟨ξ i, hξ i⟩) hpos
  let N := a + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hqn : 1 ≤ q * N := Nat.mul_pos (by omega) (by omega)
  have hden : 1 ≤ (q * N) * d := Nat.mul_pos (by omega) (by omega)
  have hFmul : (N • F).IsEffective := cartier_nsmul_isEffective F hF N
  let R := cartierPullback p (N • M) - N • F
  have hR : CartierIsGloballyGenerated R := by
    dsimp [R]
    rw [cartierPullback_nsmul, ← nsmul_sub]
    exact cartierIsGloballyGenerated_nsmul _ hfree N
  obtain ⟨s, hs, k, η, hη, hηinj, _, _, hsnc', _, hdis, _, hcoeff, _, _⟩ :=
    cartierIsGloballyGenerated_exists_boundary_compatible_perturbation B R hR ξ hsnc hsupport
  obtain ⟨t, ht, hzero⟩ := proper_birational_exists_fixed_part_section_descent
    p hnorm hp.2 (N • M) (N • F) hFmul s hs
  let G := cartierSectionZeroDivisor (N • M) t ht
  let D' := (q * N) • D + (d * a) • G
  let B' := crepantBoundaryCartier p hp cX fX ((q * N) * d) D' cT etaleCharts_cover
  have hboundary : B' = (q * N) • B + (d * a) • (N • F + cartierSectionZeroDivisor R s hs) := by
    dsimp [B', D', G, B]
    rw [crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul, hzero]
  have hinj' : Function.Injective (Fin.append ξ η) :=
    Fin.append_injective_iff.mpr ⟨hinj, hηinj, fun i j h =>
      Set.disjoint_left.mp hdis ⟨i, rfl⟩ ⟨j, h.symm⟩⟩
  have hprime : ∀ j, Order.coheight (Fin.append ξ η j) = 1 := by
    intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hξ j
    · simpa using hη j
  have hformula (z : CodimensionOnePoint T) : cartierCoefficient B' (z : T) =
      ((q * N : ℕ) : ℤ) * cartierCoefficient B (z : T) +
        ((d * a : ℕ) : ℤ) * ((N : ℤ) * cartierCoefficient F (z : T) +
          if (z : T) ∈ Set.range η then 1 else 0) := by
    rw [hboundary, cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_nsmul,
      cartierCoefficient_add, cartierCoefficient_nsmul, hcoeff]
  have hbase (z : CodimensionOnePoint T) : (q : ℤ) * cartierCoefficient B (z : T) +
      ((d * a : ℕ) : ℤ) * cartierCoefficient F (z : T) ≤ ((q * d : ℕ) : ℤ) := by
    by_cases hz : (z : T) ∈ Set.range ξ
    · obtain ⟨j, hj⟩ := hz
      simpa only [hj] using hupper j
    · rw [hsupport z hz, hFsupp z hz, mul_zero, mul_zero, add_zero]
      positivity
  have hnewsmall : ((d * a : ℕ) : ℤ) < (((q * N) * d : ℕ) : ℤ) := by
    have hn : a < q * N := hsmall
    have hm := Nat.mul_lt_mul_of_pos_left hn (by omega : 0 < d)
    exact_mod_cast (by simpa only [Nat.mul_comm d, Nat.mul_left_comm, Nat.mul_assoc] using hm)
  have hnew (z : CodimensionOnePoint T) (hz : (z : T) ∈ Set.range η) :
      cartierCoefficient B' (z : T) = ((d * a : ℕ) : ℤ) := by
    have hn : (z : T) ∉ Set.range ξ := fun h => Set.disjoint_left.mp hdis h hz
    rw [hformula, hsupport z hn, hFsupp z hn, ite_eq_left hz]
    ring
  have hbound (z : CodimensionOnePoint T) : cartierCoefficient B' (z : T) ≤ (((q * N) * d : ℕ) : ℤ) := by
    by_cases hz : (z : T) ∈ Set.range η
    · rw [hnew z hz]
      exact hnewsmall.le
    · rw [hformula, ite_eq_right hz]
      have hmul := mul_le_mul_of_nonneg_left (hbase z) (by omega : (0 : ℤ) ≤ N)
      push_cast at hmul ⊢
      nlinarith
  have hcrit (z : CodimensionOnePoint T)
      (hz : cartierCoefficient B' (z : T) = (((q * N) * d : ℕ) : ℤ)) :
      0 < cartierCoefficient F (z : T) := by
    have hn : (z : T) ∉ Set.range η := by
      intro h
      rw [hnew z h] at hz
      omega
    have hf := hg z
    by_contra hnot
    have hf0 : cartierCoefficient F (z : T) = 0 := by omega
    have he := hformula z
    rw [ite_eq_right hn, hf0] at he
    have hlt := mul_lt_mul_of_pos_left (hb z) (by omega : (0 : ℤ) < q * N)
    push_cast at he hz hlt
    nlinarith
  have hsupp' (z : CodimensionOnePoint T) (hz : (z : T) ∉ Set.range (Fin.append ξ η)) :
      cartierCoefficient B' (z : T) = 0 := by
    have hold : (z : T) ∉ Set.range ξ := by
      rintro ⟨j, hj⟩
      exact hz ⟨Fin.castAdd k j, by simpa using hj⟩
    have hnew : (z : T) ∉ Set.range η := by
      rintro ⟨j, hj⟩
      exact hz ⟨Fin.natAdd r j, by simpa using hj⟩
    rw [hformula, hsupport z hold, hFsupp z hold, ite_eq_right hnew]
    ring
  have hEff : LogPairBoundaryEffective cX fX ((q * N) * d) D' :=
    logPairBoundaryEffective_add_effective cX fX ((q * N) * d) ((q * N) • D) ((d * a) • G)
      ((logPairBoundaryEffective_scale_denominator_iff cX fX d (q * N) hqn D).mpr heff)
      (cartier_nsmul_isEffective G (cartierSectionZeroDivisor_isEffective _ _ _) (d * a))
  have hLc : LogPairIsLogCanonical cX fX ((q * N) * d) D' :=
    (logPairIsLogCanonical_iff_crepant_snc_coefficients p hp cX fX _ hden D' cT
      (Fin.append ξ η) hinj' hprime hsnc' hsupp').mpr (fun j => hbound ⟨_, hprime j⟩)
  have hEnd : cartierCoefficient B' (ξ i) = (((q * N) * d : ℕ) : ℤ) := by
    have hn : ξ i ∉ Set.range η := fun h => Set.disjoint_left.mp hdis ⟨i, rfl⟩ h
    rw [hformula ⟨ξ i, hξ i⟩, ite_eq_right hn]
    have hmul := congrArg (fun z : ℤ => (N : ℤ) * z) heq
    push_cast at hmul ⊢
    nlinarith
  have hNot : ¬ LogPairIsKlt cX fX ((q * N) * d) D' := by
    intro h
    have hi := logPairIsKlt_crepantBoundary_coefficient_lt p hp cX fX _ D' h cT ⟨ξ i, hξ i⟩
    change cartierCoefficient B' (ξ i) < _ at hi
    rw [hEnd] at hi
    exact lt_irrefl _ hi
  refine ⟨a, q, N, ha, hq, rfl, hsmall, t, ht, hEff, hLc, hNot, ?_⟩
  intro x hxZ
  apply (logPairIsKltOverBasePoint_iff_crepant_snc_coefficients p hp (𝟙 X) x
    cX fX _ hden D' cT (Fin.append ξ η) hinj' hprime hsnc' hsupp').mpr
  intro j hxj
  let z : CodimensionOnePoint T := ⟨Fin.append ξ η j, hprime j⟩
  have hb' := hbound z
  by_contra hn
  have he : cartierCoefficient B' (z : T) = (((q * N) * d : ℕ) : ℤ) := by
    change ¬ cartierCoefficient B' (z : T) < _ at hn
    omega
  have hzZ := hcenters z (hcrit z he)
  apply hxZ
  apply (specializes_iff_mem_closure.mpr (show x ∈ closure ({p (z : T)} : Set X) from by
    simpa only [Category.comp_id] using hxj)).mem_closed Z.isClosed hzZ

end MixedFujita
