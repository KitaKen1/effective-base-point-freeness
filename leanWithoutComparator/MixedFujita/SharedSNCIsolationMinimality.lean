/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperSNCCriticalCenterRetention
public import MixedFujita.SharedSNCLCCenterIsolation

/-! 共有SNCモデルでの孤立化後の最小性保持。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u v
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The actual klt-anchor isolation construction RETAINS genuine OLD minimality on the new pair, by all-test critical retention. No new minimality certificate is input. -/
theorem shared_snc_klt_anchor_isolates_and_retains_minimal_lc_center
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
      (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d' D' V → V ≤ Z → V = Z) ∧
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
  have hretained (i : Fin r)
      (hi : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d' D' cT etaleCharts_cover) (ξ i) = d') :
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = d := by
    rw [heq] at hi
    exact (hcritical i hi).1
  have hminNew : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d' D' V → V ≤ Z → V = Z :=
    minimal_lc_center_of_shared_snc_critical_index_containment ρ hρ c f d d' hd' D D' cT
      ξ hinj hξ hsnc hsuppD hsupp (fun i => by rw [heq]; exact hle i) hretained hlc Z hmin
  have heff' := logPairBoundaryEffective_add_effective c f d' (q • (N • D + A)) (p • M)
    hscaled (cartierIsEffective_nsmul M hM p)
  refine ⟨heff', hlc', hZ, original_nef_ample_adjoint_all_large K L D' hL d' b
    (hamp N (le_trans (le_max_right _ _) hN)), hminNew, fun x => ?_⟩
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
