/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FiniteCenterIdealIsolationMinimality
public import MixedFujita.InternalMinimalLCCenterIsolation

/-! 元の最小lc中心から全lc中心が一意な孤立化を内部構成。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

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


/-- FULL original minimal-lc-center isolation now internally proves that EVERY actual lc center of the new pair equals the SAME original center. No model, perturbation, critical-index/minimality certificate, KV or center normality is supplied. -/
theorem minimal_lc_center_klt_anchor_constructs_exact_nonKlt_isolation_with_unique_center
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D A : CartierDivisor X) (hD : LogPairBoundaryEffective c f d D)
    (hA : LogPairBoundaryEffective c f d A) (hklt : LogPairIsKlt c f d A)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (L : CartierDivisor X) (hL : CartierIsNef K L) (b : ℕ)
    (hH : CartierIsAmpleProj K ((d * b) • L - D)) :
    ∃ d' : ℕ, 1 ≤ d' ∧ ∃ D' : CartierDivisor X,
      LogPairBoundaryEffective c f d' D' ∧ LogPairIsLogCanonical c f d' D' ∧
      LogPairIsLogCanonicalCenter c f d' D' Z ∧
      (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d' * m) • L - D')) ∧
      (∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d' D' V → V = Z) ∧
      ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d' D') ↔ x ∈ Z := by
  classical
  let H := (d * b) • L - D
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hIZ : I.support = Z := SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)
  obtain ⟨x₀, hx₀⟩ := (logPairIsLogCanonicalCenter_isIrreducible c f d D Z hZ).nonempty
  have hnot : ¬ LogPairIsKlt c f d D := by
    intro h
    exact logPairIsLogCanonicalCenter_not_kltOverBasePoint c f d D Z hZ x₀ hx₀
      (((logPairIsKlt_iff_forall_basePoint (𝟙 X) c f d D).mp h) x₀)
  have hcov : CodimOneChartCovered n K X :=
    normal_codimOneChartCovered (K := K) (etaleChart_topologicalKrullDim c) hnorm
  obtain ⟨J, _, _, hgenJ, _, _, _, _, _, hNKJ, _, _, _⟩ :=
    lc_pair_exists_unique_reduced_nonKlt_subscheme K hn hnorm hcov ⟨H, hH⟩ c f d hd D hD hZ.1 hnot
  have hZJ := logCanonicalCenter_le_nonKlt_support c f d D J hNKJ Z hZ
  have hgenZ : genericPoint X ∉ Z := fun h => hgenJ (hZJ h)
  have hgenI : genericPoint X ∉ I.support := by simpa only [hIZ] using hgenZ
  obtain ⟨a₀, hfamily⟩ := ample_ideal_finite_sections_common_zero_locus_exact_support H hH I
  let P := (a₀ + 1) • H
  obtain ⟨k, s, hzero, hunit, _⟩ := hfamily (a₀ + 1) (by omega)
  obtain ⟨i₀, hi₀⟩ := hunit (genericPoint X) hgenI
  have hs₀ : s i₀ ≠ 0 := (cartierLocalCoefficient_ne_zero_iff P (genericPoint X) _ _ _).mp hi₀.ne_zero
  obtain ⟨r, e, he, hcover⟩ := finite_family_exists_nonzero_index_subfamily k s
  let v : Fin (r + 1) → Γ(P.sheaf, ⊤) := Fin.cons (s i₀) (fun i => s (e i))
  have hv : ∀ i, v i ≠ 0 := fun i => Fin.cases hs₀ (fun j => he j) i
  have hvzero : ∀ i, modulePullbackGlobalSections I.subschemeι P.sheaf (v i) = 0 :=
    fun i => Fin.cases (hzero i₀) (fun j => hzero (e j)) i
  have hbase : ((cartierSectionBaseIdeal P v hv).support : Set X) ⊆ Z := by
    intro x hx
    by_contra hxZ
    have hxZ' : x ∉ Z := hxZ
    have hxI : x ∉ I.support := by simpa only [hIZ] using hxZ'
    obtain ⟨j, hj⟩ := hunit x hxI
    have hsj : s j ≠ 0 := (cartierLocalCoefficient_ne_zero_iff P x _ _ _).mp hj.ne_zero
    obtain ⟨l, hl⟩ := hcover j hsj
    rw [cartierSectionBaseIdeal_support (K := K), Set.mem_iInter] at hx
    have hz := hx l.succ
    change x ∈ cartierSectionZeroLocus P (s (e l)) at hz
    rw [hl] at hz
    exact hz ((mem_cartierSectionNonvanishingOpen_iff_localCoefficient P (s j) x _ _).mpr hj)
  obtain ⟨u, hu, _, p, q, N₀, _, hq, hpair⟩ :=
    original_finite_center_ideal_system_constructs_isolated_lc_pair_with_minimality K hnorm c f d hd D A hD hA hklt
      Z hZ hmin P r v hv hvzero hbase L hL b hH
  obtain ⟨heff', hlc', hZ', hamp, hmin', hNK⟩ := hpair N₀ le_rfl
  refine ⟨q * (N₀ + 1) * d, Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega),
    _, heff', hlc', hZ', hamp, ?_, hNK⟩
  intro V hV
  apply hmin' V hV
  intro x hx
  exact (hNK x).mp (logPairIsLogCanonicalCenter_not_kltOverBasePoint c f _ _ V hV x hx)

end MixedFujita
