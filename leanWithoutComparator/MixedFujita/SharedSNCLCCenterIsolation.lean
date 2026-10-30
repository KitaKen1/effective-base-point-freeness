/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteLCKltAnchorArithmetic
public import MixedFujita.PairNaturalCombination
public import MixedFujita.AnchorOriginalAdjointAmpleness
public import MixedFujita.CrepantSNCBasePointKlt
public import MixedFujita.SNCLogCanonicalCenterCover
public import MixedFujita.RationalNefBigPullbackKltRepresentative

/-! 実共有SNCモデルと有効Mから元の非klt集合を極小中心へ孤立化。 See reports/check-267-klt-anchor-center-isolation.json for the verified scope. A fixed rational perturbation ratio and all-large mixing with an actual klt anchor retain only OLD positive-perturbation critical components and preserve ORIGINAL L ample adjoints. On a SUPPLIED actual shared proper SNC model with a SUPPLIED actual effective source perturbation and critical-placement/positivity inputs, the entire ORIGINAL nonKlt locus equals the chosen minimal lc center. The exact reduced center ideal is internally identified, and EXPLICIT usual H1 KV yields original Cartier and all-large ORIGINAL mL restriction lifting. Constructing the isolation perturbation/model/placement/positivity and numerical-zero center nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- On an ACTUAL shared SNC model, a klt anchor isolates a chosen OLD minimal
lc center as the ENTIRE ORIGINAL non-klt locus. The effective perturbation is
an actual source Cartier divisor; its positive old-critical primes lie over
that center and at least one exists. A fixed rational endpoint and all-large
mixing are internal, preserving ALL large ORIGINAL L-adjoint ampleness.
The required source perturbation/model data remain explicit in this criterion. -/
theorem shared_snc_klt_anchor_isolates_minimal_lc_center
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D A : CartierDivisor X) (hD : LogPairBoundaryEffective c f d D)
    (hlc : LogPairIsLogCanonical c f d D) (hA : LogPairBoundaryEffective c f d A)
    (hklt : LogPairIsKlt c f d A) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppD : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (z : T) = 0)
    (hsuppA : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d A cT etaleCharts_cover) (z : T) = 0)
    (Z : Closeds X)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (M : CartierDivisor X) (hM : M.IsEffective)
    (hsuppM : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ M) (z : T) = 0)
    (hplace : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = d →
      0 < cartierCoefficient (cartierPullback ρ M) (ξ i) →
        (⟨closure ({ρ (ξ i)} : Set X), isClosed_closure⟩ : Closeds X) ≤ Z)
    (hpos : ∃ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = d ∧
      0 < cartierCoefficient (cartierPullback ρ M) (ξ i))
    (L : CartierDivisor X) (hL : CartierIsNef K L) (b : ℕ)
    (hH : CartierIsAmpleProj K ((d * b) • L - D)) :
    ∃ p q N₀ : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ ∀ N : ℕ, N₀ ≤ N →
      let d' := q * (N + 1) * d
      let D' := q • (N • D + A) + p • M
      LogPairBoundaryEffective c f d' D' ∧ LogPairIsLogCanonical c f d' D' ∧
      LogPairIsLogCanonicalCenter c f d' D' Z ∧
      (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d' * m) • L - D')) ∧
      ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d' D') ↔ x ∈ Z := by
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  let C := crepantBoundaryCartier ρ hρ c f d A cT etaleCharts_cover
  let β := fun i => cartierCoefficient B (ξ i)
  let γ := fun i => cartierCoefficient C (ξ i)
  let g := fun i => cartierCoefficient (cartierPullback ρ M) (ξ i)
  have hb (i : Fin r) : β i ≤ (d : ℤ) :=
    logPairIsLogCanonical_crepantBoundary_coefficient_le ρ hρ c f d D hlc cT ⟨ξ i, hξ i⟩
  have hc (i : Fin r) : γ i < (d : ℤ) :=
    logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d A hklt cT ⟨ξ i, hξ i⟩
  have hg (i : Fin r) : 0 ≤ g i :=
    cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ M hM) (ξ i)
  obtain ⟨p, q, N₁, hp, hq, i₀, hb₀, hg₀, hcoef⟩ :=
    finite_lc_klt_anchor_isolating_coefficients β γ g d hd hb hc hg hpos
  obtain ⟨N₂, hamp⟩ := lc_anchor_perturbed_original_adjoint_eventually_ample K L D A M d b p q hq hH
  refine ⟨p, q, max N₁ N₂, hp, hq, fun N hN => ?_⟩
  dsimp only
  let d' := q * (N + 1) * d
  let D' := q • (N • D + A) + p • M
  have hd' : 1 ≤ d' := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hB : crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover =
      q • (N • B + C) + p • cartierPullback ρ M := by
    dsimp only [d', D', B, C]
    rw [show q * (N + 1) * d = q * (N * d + 1 * d) by ring,
      crepantBoundaryCartier_add_source, crepantBoundaryCartier_scale_denominator,
      cartierPullback_nsmul]
    have hc := crepantBoundaryCartier_natural_combination ρ hρ c f d d N 1 D A cT etaleCharts_cover
    simpa only [one_smul] using congrArg (fun F : CartierDivisor T => q • F + p • cartierPullback ρ M) hc
  have hsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover) (z : T) = 0 := by
    intro z hz
    rw [hB, cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_add,
      cartierCoefficient_nsmul, cartierCoefficient_nsmul, hsuppD z hz, hsuppA z hz, hsuppM z hz]
    simp
  have heq (i : Fin r) : cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover) (ξ i) =
      (q : ℤ) * ((N : ℤ) * β i + γ i) + (p : ℤ) * g i := by
    rw [hB, cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_add,
      cartierCoefficient_nsmul, cartierCoefficient_nsmul]
  obtain ⟨hle, heq₀, hcritical⟩ := hcoef N (le_trans (le_max_left _ _) hN)
  have hlc' : LogPairIsLogCanonical c f d' D' :=
    (logPairIsLogCanonical_iff_crepant_snc_coefficients ρ hρ c f d' hd' D' cT ξ hinj hξ hsnc hsupp).mpr
      (fun i => by rw [heq]; exact hle i)
  have hcenter (i : Fin r)
      (hi : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover) (ξ i) = d') :
      (⟨closure ({ρ (ξ i)} : Set X), isClosed_closure⟩ : Closeds X) = Z := by
    rw [heq] at hi
    obtain ⟨hbi, hgi⟩ := hcritical i hi
    exact hmin _ (crepant_critical_prime_is_logCanonicalCenter ρ hρ c f d D hlc cT (ξ i) (hξ i) hbi)
      (hplace i hbi hgi)
  have hcrit₀ : cartierCoefficient
      (crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover) (ξ i₀) = d' := (heq i₀).trans heq₀
  have hZ : LogPairIsLogCanonicalCenter c f d' D' Z :=
    (hcenter i₀ hcrit₀) ▸ crepant_critical_prime_is_logCanonicalCenter ρ hρ c f d' D' hlc' cT
      (ξ i₀) (hξ i₀) hcrit₀
  have hmix := logPairBoundaryEffective_natural_combination c f d d N 1 D A hD hA
  have hmix' : LogPairBoundaryEffective c f ((N + 1) * d) (N • D + A) := by
    simpa only [one_smul, one_mul, add_mul] using hmix
  have hscaled : LogPairBoundaryEffective c f d' (q • (N • D + A)) := by
    simpa only [d', Nat.mul_assoc] using
      ((logPairBoundaryEffective_scale_denominator_iff c f ((N + 1) * d) q hq _).mpr hmix')
  have heff' := logPairBoundaryEffective_add_effective c f d' (q • (N • D + A)) (p • M)
    hscaled (cartierIsEffective_nsmul M hM p)
  refine ⟨heff', hlc', hZ, original_nef_ample_adjoint_all_large K L D' hL d' b
    (hamp N (le_trans (le_max_right _ _) hN)), fun x => ?_⟩
  constructor
  · intro hnot
    by_contra hx
    apply hnot
    apply (logPairIsKltOverBasePoint_iff_crepant_snc_coefficients ρ hρ (𝟙 X) x c f d' hd' D' cT
      ξ hinj hξ hsnc hsupp).mpr
    intro i hi
    have hb' : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover) (ξ i) ≤ d' :=
      by rw [heq]; exact hle i
    by_contra hnlt
    have hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover) (ξ i) = d' := by omega
    apply hx
    rw [← hcenter i hcrit]
    change x ∈ closure ({ρ (ξ i)} : Set X)
    simpa only [Category.comp_id] using hi
  · intro hx
    exact logPairIsLogCanonicalCenter_not_kltOverBasePoint c f d' D' Z hZ x hx

end MixedFujita
