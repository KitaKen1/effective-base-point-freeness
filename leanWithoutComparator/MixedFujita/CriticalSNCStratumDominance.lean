/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NonproperCriticalCenterUniqueness
public import MixedFujita.ToricExtractionPrime
public import MixedFujita.SNCStrataGenericPoints
public import MixedFujita.SNCComponentCartier
public import MixedFujita.CrepantDiscrepancyComposition
public import MixedFujita.CrepantBoundaryPerturbation

/-! 指示重みSNC抽出による全臨界交差一般点の支配性。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

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


/-- EVERY generic component of an intersection of actual critical SNC
members dominates the unique isolated center. The extraction map need not
be proper: its exact center is forced by the positive-threshold argument. -/
theorem isolated_unique_lc_center_critical_snc_stratum_dominates
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hunique : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V = Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔ x ∈ Z)
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (s : Finset (Fin r)) (hs : s.Nonempty)
    (hcrit : ∀ i ∈ s,
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    (η : T) (hη : ∀ i ∈ s, η ∈ closure ({ξ i} : Set T))
    (hmax : ∀ η' : T, (∀ i ∈ s, η' ∈ closure ({ξ i} : Set T)) → η' ⤳ η → η' = η) :
    (⟨closure ({ρ η} : Set X), isClosed_closure⟩ : Closeds X) = Z := by
  classical
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  let W : Fin r → ℕ := fun i => if i ∈ s then 1 else 0
  obtain ⟨i₀, hi₀⟩ := hs
  have hW : W ≠ 0 := by
    intro hz
    have hh := congrFun hz i₀
    simp only [W, ite_eq_left hi₀, Pi.zero_apply, one_ne_zero] at hh
  have hWy : ∀ j, W j ≠ 0 → η ∈ closure ({ξ j} : Set T) := by
    intro j hj
    exact hη j (by by_contra hn; exact hj (ite_eq_right hn))
  obtain ⟨U, hUi, hUn, hUo, hUs, α, hdom, hover, hα, cU, e, g, W',
    hg, hWW, hclos, hord, hdisc⟩ := exists_snc_extraction_prime ξ hinj hξ hsnc η W hW hWy
  let := hUi
  let := hUn
  let := hUo
  let := hUs
  let := hdom
  let := hover
  have hprod : g * W' i₀ = 1 := by simpa only [W, ite_eq_left hi₀] using (hWW i₀).symm
  have hg1 : g = 1 := by
    have hh := Nat.le_of_dvd Nat.zero_lt_one (show g ∣ 1 from ⟨W' i₀, hprod.symm⟩)
    omega
  have hW' (j : Fin r) : W' j = W j := by simpa only [hg1, one_mul] using (hWW j).symm
  obtain ⟨E, hE, hEI, hEc⟩ := exists_snc_component_cartier ξ hξ hsnc
  have hcomponentOrder (i : Fin r) :
      cartierCoefficient (cartierPullback α (E i)) (e : U) = (W' i : ℤ) := by
    have hEsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (E i) (z : T) = 0 := by
      intro z hz
      rw [hEc]
      exact ite_eq_right (fun h => hz ⟨i, h.symm⟩)
    rw [hord (E i) hEsupp]
    have heq (j : Fin r) : cartierCoefficient (E i) (ξ j) = if j = i then 1 else 0 := by
      simpa only [hinj.eq_iff] using hEc i ⟨ξ j, hξ j⟩
    simp_rw [heq]
    simp
  have hαemem : ∀ i ∈ s, α (e : U) ∈ closure ({ξ i} : Set T) := by
    intro i hi
    have hp : 0 < cartierCoefficient (cartierPullback α (E i)) (e : U) := by
      rw [hcomponentOrder, hW']
      simp only [W, ite_eq_left hi, Nat.cast_one, zero_lt_one]
    have hh := positive_effective_pullback_prime_center_le_source_support α (E i) (hE i) (e : U) hp
    rw [hEI i] at hh
    have hm := hh (subset_closure (show α (e : U) ∈ ({α (e : U)} : Set T) from rfl))
    simpa only [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_mk] using hm
  have hαe : α (e : U) = η := hmax _ hαemem (specializes_iff_mem_closure.mpr hclos)
  let B := crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover
  have hsum : ∑ j, cartierCoefficient B (ξ j) * (W' j : ℤ) = (d : ℤ) * ∑ j, (W' j : ℤ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ s
    · rw [hcrit j hj]
    · rw [hW']
      simp only [W, ite_eq_right hj, Nat.cast_zero, mul_zero]
  have hh := hdisc cT (crepantPullbackFormUnit ρ hρ c f cT) d B hsupp
  rw [hsum, sub_self] at hh
  have hnegative :
      cartierCoefficient (logDiscrepancyDivisor n α hα cT
        (crepantPullbackFormUnit ρ hρ c f cT) d
        (d • (smoothCanonicalDivisor cT + principalCartierDivisor T
          (crepantPullbackFormUnit ρ hρ c f cT)) + B) cU etaleCharts_cover) (e : U) = -(d : ℤ) := by
    omega
  dsimp only [B] at hnegative
  rw [crepantBoundaryCartier_smooth_recombine,
    ← logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cU etaleCharts_cover] at hnegative
  have hz := isolated_unique_lc_center_nonproper_critical_prime_center hnorm c f d hd D hlc Z hunique hNK
    H hH (α ≫ ρ) (dominantFunctionFieldAlgHom_comp_bijective ρ α hρ hα) cU e hnegative
  change (⟨closure ({ρ (α (e : U))} : Set X), isClosed_closure⟩ : Closeds X) = Z at hz
  simpa only [hαe] using hz


/-- Every point on a nonempty selected critical intersection admits an
actual generic component through it whose image is dense in the exact
isolated center. No component dominance is an input. -/
theorem isolated_unique_lc_center_critical_intersection_generic_dominance
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hunique : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V = Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔ x ∈ Z)
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (s : Finset (Fin r)) (hs : s.Nonempty)
    (hcrit : ∀ i ∈ s,
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    (y : T) (hy : ∀ i ∈ s, y ∈ closure ({ξ i} : Set T)) :
    ∃ η : T, (∀ i ∈ s, η ∈ closure ({ξ i} : Set T)) ∧ η ⤳ y ∧
      (∀ η' : T, (∀ i ∈ s, η' ∈ closure ({ξ i} : Set T)) → η' ⤳ η → η' = η) ∧
      (⟨closure ({ρ η} : Set X), isClosed_closure⟩ : Closeds X) = Z := by
  let w : Fin r → ℝ := fun i => if i ∈ s then 1 else 0
  have hwy : ∀ i, w i ≠ 0 → y ∈ closure ({ξ i} : Set T) := by
    intro i hi
    exact hy i (by by_contra hn; exact hi (ite_eq_right hn))
  obtain ⟨η, hη, hηy, hmax⟩ := exists_stratum_generic_point ξ w y hwy
  have hm : ∀ i ∈ s, η ∈ closure ({ξ i} : Set T) := fun i hi => hη i (by simpa only [w, ite_eq_left hi] using (one_ne_zero : (1 : ℝ) ≠ 0))
  have hx : ∀ η' : T, (∀ i ∈ s, η' ∈ closure ({ξ i} : Set T)) → η' ⤳ η → η' = η := by
    intro η' hη' hsp
    exact hmax η' (fun i hi => hη' i (by by_contra hn; exact hi (ite_eq_right hn))) hsp
  exact ⟨η, hm, hηy, hx,
    isolated_unique_lc_center_critical_snc_stratum_dominates ρ hρ hnorm c f d hd D hlc Z hunique hNK
      H hH cT ξ hinj hξ hsnc hsupp s hs hcrit η hm hx⟩

end MixedFujita
