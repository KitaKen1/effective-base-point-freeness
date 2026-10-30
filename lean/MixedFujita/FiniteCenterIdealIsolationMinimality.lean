/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SharedSNCIsolationMinimality
public import MixedFujita.FiniteCenterIdealIsolation

/-! 元の有限中心イデアル系による最小性を保つ孤立化。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

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


/-- The SAME original finite center-ideal system internally constructs the model, perturbation and isolated lc pair WITH retained genuine minimality. -/
theorem original_finite_center_ideal_system_constructs_isolated_lc_pair_with_minimality
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D A : CartierDivisor X) (hD : LogPairBoundaryEffective c f d D)
    (hA : LogPairBoundaryEffective c f d A) (hklt : LogPairIsKlt c f d A)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (P : CartierDivisor X) (k : ℕ) (s : Fin (k + 1) → Γ(P.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (hzero : ∀ i, modulePullbackGlobalSections (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι P.sheaf (s i) = 0)
    (hbase : ((cartierSectionBaseIdeal P s hs).support : Set X) ⊆ Z)
    (L : CartierDivisor X) (hL : CartierIsNef K L) (b : ℕ)
    (hH : CartierIsAmpleProj K ((d * b) • L - D)) :
    ∃ (u : Γ(P.sheaf, ⊤)) (hu : u ≠ 0),
      modulePullbackGlobalSections (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι P.sheaf u = 0 ∧
      ∃ p q N₀ : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ ∀ N : ℕ, N₀ ≤ N →
        let d' := q * (N + 1) * d
        let D' := q • (N • D + A) + p • cartierSectionZeroDivisor P u hu
        LogPairBoundaryEffective c f d' D' ∧ LogPairIsLogCanonical c f d' D' ∧
        LogPairIsLogCanonicalCenter c f d' D' Z ∧
        (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d' * m) • L - D')) ∧
        (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d' D' V → V ≤ Z → V = Z) ∧
        ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d' D') ↔ x ∈ Z := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let : I.subscheme.Over (Spec (CommRingCat.of K)) := ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : I.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsIntegral I.subscheme := logCanonicalCenter_reduced_subscheme_isIntegral c f d D Z hZ
  let E := fun i => cartierSectionZeroDivisor P (s i) (hs i)
  have hE (i : Fin (k + 1)) : (E i).IsEffective := cartierSectionZeroDivisor_isEffective P (s i) (hs i)
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hproper, _, hρ, cT, r, ξ,
      hinj, hξ, hsnc, hsuppD, hdiff, _, _, _, _, F, hF, hFI, hFsupp, _, _⟩ :=
    exists_projective_snc_model_principalizing_sum c f d D (fun _ : PUnit.{1} => A - D) E hE
      (fun i : PEmpty.{1} => i.elim) (fun i => i.elim)
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hproper
  have : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨t, _, hinc, _, _, hfree⟩ :=
    principalized_original_finite_system_exists_residual_basePointFree ρ P s hs F hF hFI
  obtain ⟨a, _, hat, q₀, η, hηinj, hη, hsnc', hdis, hcoeff⟩ :=
    residual_first_nonzero_boundary_compatible_snc_parameter (cartierPullback ρ P - F) k t hfree ξ hsnc
  let u := ∑ i, a i • s i
  let v := ∑ i, a i • t i
  let ι := cartierEffectiveInclusion (cartierPullback ρ P) F hF
  have hi : Scheme.Modules.Hom.app ι ⊤ v = cartierDominantPullbackSection ρ P u :=
    residual_original_linear_combination_inclusion ρ P s F hF t hinc a
  let : Mono ι := cartierEffectiveInclusion_mono (cartierPullback ρ P) F hF
  have hv : Scheme.Modules.Hom.app ι ⊤ v ≠ 0 :=
    (map_ne_zero_iff _ (CohomologyAux.app_injective_of_mono ι ⊤)).mpr hat
  have hu : u ≠ 0 := by
    intro hz
    apply hv
    rw [hi, hz]
    exact (cartierDominantPullbackLinear ρ K P).map_zero
  let M := cartierSectionZeroDivisor P u hu
  have hM : M.IsEffective := cartierSectionZeroDivisor_isEffective P u hu
  let G := cartierSectionZeroDivisor (cartierPullback ρ P - F) v hat
  have hMG : cartierPullback ρ M = F + G := by
    rw [← cartierDominantPullbackSection_zeroDivisor ρ P u hu]
    exact cartier_fixed_part_inclusion_zeroDivisor (cartierPullback ρ P) F hF v hat _
      (cartierDominantPullbackSection_ne_zero ρ P u hu) hi
  have hu0 : modulePullbackGlobalSections I.subschemeι P.sheaf u = 0 := by
    have hzI (i) : modulePullbackGlobalSections I.subschemeι P.sheaf (s i) = 0 := hzero i
    dsimp only [u]
    rw [map_sum]
    simp only [modulePullbackGlobalSections_smul_base, hzI, smul_zero, Finset.sum_const_zero]
  have hcontain : Z ≤ (effectiveCartierIdealSheaf M hM).support := by
    have hIZ : I.support = Z := SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
    rw [← hIZ]
    by_contra hn
    exact ((natural_restriction_ne_zero_iff_not_le_zero_divisor_support (K := K) I P u hu).mpr hn) hu0
  let ξ' := Fin.append ξ η
  have hinj' : Function.Injective ξ' := Fin.append_injective_iff.mpr
    ⟨hinj, hηinj, fun i j h => Set.disjoint_left.mp hdis ⟨i, rfl⟩ ⟨j, h.symm⟩⟩
  have hξ' : ∀ i, Order.coheight (ξ' i) = 1 := by
    intro i
    exact Fin.addCases (fun j => by simpa only [ξ', Fin.append_left] using hξ j)
      (fun j => by simpa only [ξ', Fin.append_right] using hη j) i
  have hold : Set.range ξ ⊆ Set.range ξ' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.castAdd q₀ i, by simp only [ξ', Fin.append_left]⟩
  have hnew : Set.range η ⊆ Set.range ξ' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.natAdd r i, by simp only [ξ', Fin.append_right]⟩
  have hsuppD' (z : CodimensionOnePoint T) (hz : (z : T) ∉ Set.range ξ') :
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (z : T) = 0 :=
    hsuppD z (fun h => hz (hold h))
  have hAD : D + (A - D) = A := by abel
  have hBA : crepantBoundaryCartier ρ hρ c f d A cT etaleCharts_cover =
      crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover + cartierPullback ρ (A - D) := by
    simpa only [hAD] using crepantBoundaryCartier_add_source ρ hρ c f d D (A - D) cT etaleCharts_cover
  have hsuppA' (z : CodimensionOnePoint T) (hz : (z : T) ∉ Set.range ξ') :
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d A cT etaleCharts_cover) (z : T) = 0 := by
    rw [hBA, cartierCoefficient_add, hsuppD' z hz, hdiff PUnit.unit z (fun h => hz (hold h)), add_zero]
  have hsuppM' (z : CodimensionOnePoint T) (hz : (z : T) ∉ Set.range ξ') :
      cartierCoefficient (cartierPullback ρ M) (z : T) = 0 := by
    rw [hMG, cartierCoefficient_add, hFsupp z (fun h => hz (hold h)), hcoeff z,
      ite_eq_right (fun h => hz (hnew h)), add_zero]
  have hplace (i : Fin (r + q₀))
      (hcrit : cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ' i) = d)
      (hpos : 0 < cartierCoefficient (cartierPullback ρ M) (ξ' i)) :
      (⟨closure ({ρ (ξ' i)} : Set X), isClosed_closure⟩ : Closeds X) ≤ Z := by
    have hiold : ξ' i ∈ Set.range ξ := by
      by_contra hn
      rw [hsuppD ⟨ξ' i, hξ' i⟩ hn] at hcrit
      omega
    have hinew : ξ' i ∉ Set.range η := fun h => Set.disjoint_left.mp hdis hiold h
    have hGzero : cartierCoefficient G (ξ' i) = 0 := by rw [hcoeff ⟨ξ' i, hξ' i⟩, ite_eq_right hinew]
    have hρZ : ρ (ξ' i) ∈ Z := by
      by_contra hx
      have hzF := principalized_fixed_coefficient_zero_over_exterior_point ρ (cartierSectionBaseIdeal P s hs)
        F hF hFI Z hbase (ρ (ξ' i)) hx ⟨ξ' i, hξ' i⟩ (subset_closure rfl)
      rw [hMG, cartierCoefficient_add, hzF, hGzero, add_zero] at hpos
      exact lt_irrefl _ hpos
    exact closure_minimal (Set.singleton_subset_iff.mpr hρZ) Z.isClosed
  have hpos := lc_center_contained_effective_divisor_forces_snc_positive_critical_prime hnorm ρ hρ
    c f d hd D Z hZ M hM hcontain cT ξ' hinj' hξ' hsnc' hsuppD' hsuppM'
  refine ⟨u, hu, hu0, ?_⟩
  exact shared_snc_klt_anchor_isolates_and_retains_minimal_lc_center K ρ hρ c f d hd D A hD hZ.1 hA hklt cT
    ξ' hinj' hξ' hsnc' hsuppD' hsuppA' Z hmin M hM hsuppM' hplace hpos L hL b hH

end MixedFujita
