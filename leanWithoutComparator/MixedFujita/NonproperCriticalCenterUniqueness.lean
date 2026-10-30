/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleClosedSetCartierSeparation
public import MixedFujita.PositiveRationalLCThreshold
public import MixedFujita.KltNonproperBirationalTests
public import MixedFujita.LogCanonicalNonproperBirationalTests
public import MixedFujita.DVRSupportPositiveCartierCoefficient

/-! 正のlc閾値による非固有臨界テストの正確な中心。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

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


/-- A ZERO-discrepancy prime on an actual NONPROPER smooth test obstructs
every positive perturbation having positive order there. This uses the
proved all-test comparison, never a fictitious properization. -/
theorem nonproper_critical_prime_obstructs_positive_effective_perturbation
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X U : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral U] [IsLocallyNoetherian U] [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D G : CartierDivisor X)
    (cU : EtaleChart K U n) (t : CodimensionOnePoint U)
    (hcrit : cartierCoefficient (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (t : U) = -(d : ℤ))
    (hpos : 0 < cartierCoefficient (cartierPullback σ G) (t : U))
    (a q : ℕ) (ha : 1 ≤ a) (hq : 1 ≤ q) :
    ¬ LogPairIsLogCanonical c f (q * d) (q • D + (d * a) • G) := by
  intro hlc
  have hh := logPairIsLogCanonical_discrepancy_bound_on_birational_test c f (q * d)
    (Nat.mul_pos (by omega) (by omega)) (q • D + (d * a) • G) hlc σ hσ cU t
  rw [logDiscrepancyDivisor_add_source, logDiscrepancyDivisor_scale_denominator, cartierPullback_nsmul,
    cartierCoefficient_sub, cartierCoefficient_nsmul, cartierCoefficient_nsmul, hcrit] at hh
  have hp : 0 < ((d * a : ℕ) : ℤ) * cartierCoefficient (cartierPullback σ G) (t : U) :=
    mul_pos (by exact_mod_cast Nat.mul_pos (by omega : 0 < d) (by omega : 0 < a)) hpos
  push_cast at hh hp
  nlinarith


/-- With a UNIQUE actual lc center, every zero-discrepancy prime on
EVERY actual smooth birational test has that exact center, even when its
test map is NONPROPER. Ample separation and a positive lc threshold avoid
any compactification or classification of all SNC strata. -/
theorem isolated_unique_lc_center_nonproper_critical_prime_center
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X U : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsIntegral U] [IsLocallyNoetherian U] [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X)
    (hlc : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hunique : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V = Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔ x ∈ Z)
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (t : CodimensionOnePoint U)
    (hcrit : cartierCoefficient (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (t : U) = -(d : ℤ)) :
    (⟨closure ({σ (t : U)} : Set X), isClosed_closure⟩ : Closeds X) = Z := by
  classical
  let C : Closeds X := ⟨closure ({σ (t : U)} : Set X), isClosed_closure⟩
  have himage : σ (t : U) ∈ Z := by
    by_contra hx
    have hk : LogPairIsKltOverBasePoint (𝟙 X) (σ (t : U)) c f d D := by
      by_contra h
      exact hx ((hNK _).mp h)
    have hb := logPairIsKltOverBasePoint_discrepancy_bound_on_birational_test (𝟙 X) (σ (t : U))
      c f d hd D hk σ hσ cU t (by simpa only [Category.comp_id] using (show σ (t : U) ∈ closure ({σ (t : U)} : Set X) from subset_closure (Set.mem_singleton _)))
    rw [hcrit] at hb
    exact (lt_irrefl _) hb
  have hCZ : C ≤ Z := closure_minimal (Set.singleton_subset_iff.mpr himage) Z.isClosed
  by_contra hne
  have hnot : ¬ Z ≤ C := fun h => hne (le_antisymm hCZ h)
  obtain ⟨G, hG, hGne, hCG, hZG⟩ := ample_effective_cartier_separates_closed_sets H hH C Z
    ⟨σ (t : U), subset_closure rfl⟩ hnot
  obtain ⟨a, q, ha, hq, _, hLc, _, _, _, _, _, _⟩ :=
    exists_exact_positive_rational_lc_threshold_with_new_center hnorm c f d hd D hlc G hG hGne
      (fun V hV => by rw [hunique V hV]; exact hZG)
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  have hup : (t : U) ∈ (effectiveCartierIdealSheaf (cartierPullback σ G)
      (cartierPullback_isEffective σ G hG)).support := by
    rw [effectiveCartierIdealSheaf_cartierPullback σ G hG, Scheme.IdealSheafData.support_comap]
    exact hCG (subset_closure rfl)
  have hpos := effective_cartier_coefficient_pos_of_mem_support_at_dvr
    (cartierPullback σ G) (cartierPullback_isEffective σ G hG) t hup
  exact nonproper_critical_prime_obstructs_positive_effective_perturbation σ hσ c f d hd D G cU t
    hcrit hpos a q ha hq hLc

end MixedFujita
