/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCCriticalDiscrepancyRetention
public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.LCCenterEffectiveAvoidance
public import MixedFujita.MinimalLogCanonicalCenters

/-! 全実テストの臨界比較とlc中心・最小性保持。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

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


/-- A shared ACTUAL proper SNC model propagates finite critical-index
containment to every original smooth birational test prime. The actual
valuative local extension and open-stalk comparisons are constructed
internally; no common proper model or local lift is supplied. -/
theorem proper_snc_model_actual_test_critical_prime_retention
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d e : ℕ) (he : 1 ≤ e)
    (D E : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppD : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hsuppE : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (t : T) = 0)
    (hE : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) ≤ (e : ℤ))
    (hcritical : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) = (e : ℤ) →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (x : CodimensionOnePoint U)
    (hnew : cartierCoefficient (logDiscrepancyDivisor n σ hσ c f e E cU etaleCharts_cover) (x : U) = -(e : ℤ)) :
    cartierCoefficient (logDiscrepancyDivisor n σ hσ c f d D cU etaleCharts_cover) (x : U) = -(d : ℤ) := by
  let : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨W, hx, hW, α, hdom, hcomm, hα⟩ :=
    proper_birational_exists_local_birational_extension ρ σ hρ hσ (x : U)
  let : Nonempty W := ⟨⟨(x : U), hx⟩⟩
  let : IsIntegral W.toScheme := hW
  let : W.toScheme.Over (Spec (CommRingCat.of K)) := ⟨W.ι ≫ (U ↘ Spec (CommRingCat.of K))⟩
  let : W.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsDominant α := hdom
  let : IsDominant W.ι := ⟨W.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  let : SmoothOfRelativeDimension n (W.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (W.ι ≫ (U ↘ Spec (CommRingCat.of K))) := inferInstance
    simpa only [Nat.zero_add] using h
  let : α.IsOver (Spec (CommRingCat.of K)) := by
    apply (Scheme.Hom.isOver_iff (Spec (CommRingCat.of K))).mpr
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := σ) (S := Spec (CommRingCat.of K)),
      HomIsOver.comp_over (f := W.ι) (S := Spec (CommRingCat.of K))]
  have hι : Function.Bijective (dominantFunctionFieldAlgHom (K := K) W.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion W.ι
  let w : W.toScheme := ⟨(x : U), hx⟩
  have hw : Order.coheight w = 1 :=
    (coheight_eq_of_stalkMap_bijective W.ι w
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))).trans x.property
  let t : CodimensionOnePoint W.toScheme := ⟨w, hw⟩
  obtain ⟨cW⟩ : Nonempty (EtaleChart K W.toScheme n) :=
    ⟨Classical.choose (show ∃ a : EtaleChart K W.toScheme n, w ∈ a.U from
      Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := W.toScheme) (n := n)).symm ▸ Opens.mem_top w))⟩
  have hnewW : cartierCoefficient (logDiscrepancyDivisor n (W.ι ≫ σ)
      (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι) c f e E cW etaleCharts_cover)
      (t : W.toScheme) = -(e : ℤ) := by
    rw [logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ W.ι hσ hι c f e E cU cW t x.property
      (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))]
    exact hnew
  have hnewα : cartierCoefficient (logDiscrepancyDivisor n α hα cT
      (crepantPullbackFormUnit ρ hρ c f cT) e
      (e • (smoothCanonicalDivisor cT + principalCartierDivisor T (crepantPullbackFormUnit ρ hρ c f cT)) +
        crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover)
      cW etaleCharts_cover) (t : W.toScheme) = -(e : ℤ) := by
    rw [crepantBoundaryCartier_smooth_recombine,
      ← logDiscrepancyDivisor_comp ρ α hρ hα c f e E cT cW etaleCharts_cover]
    simpa only [hcomm] using hnewW
  have hold := isSNCFamily_actual_critical_prime_retention α hα cT (crepantPullbackFormUnit ρ hρ c f cT)
    d e he (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
    (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover)
    ξ hinj hξ hsnc hsuppD hsuppE hE hcritical cW t hnewα
  rw [crepantBoundaryCartier_smooth_recombine,
    ← logDiscrepancyDivisor_comp ρ α hρ hα c f d D cT cW etaleCharts_cover] at hold
  have holdW : cartierCoefficient (logDiscrepancyDivisor n (W.ι ≫ σ)
      (dominantFunctionFieldAlgHom_comp_bijective σ W.ι hσ hι) c f d D cW etaleCharts_cover)
      (t : W.toScheme) = -(d : ℤ) := by simpa only [hcomm] using hold
  rw [logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective σ W.ι hσ hι c f d D cU cW t x.property
    (ConcreteCategory.bijective_of_isIso (W.ι.stalkMap w))] at holdW
  exact holdW


/-- Actual NEW lc centers are OLD lc centers from finite critical-index containment on a shared proper SNC model. -/
theorem logCanonicalCenter_of_shared_snc_critical_index_containment
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d e : ℕ) (he : 1 ≤ e)
    (D E : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppD : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hsuppE : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (t : T) = 0)
    (hE : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) ≤ (e : ℤ))
    (hcritical : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) = (e : ℤ) →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    (hlcD : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hZ : LogPairIsLogCanonicalCenter c f e E Z) :
    LogPairIsLogCanonicalCenter c f d D Z := by
  obtain ⟨_, U, hUi, hUn, hUo, hUs, σ, hdom, hover, hproper, hσ, cU, x, hx, hdisc, hset⟩ := hZ
  let := hUi
  let := hUn
  let := hUo
  let := hUs
  let := hdom
  let := hover
  let := hproper
  refine ⟨hlcD, U, hUi, hUn, hUo, hUs, σ, hdom, hover, hproper, hσ, cU, x, hx, ?_, hset⟩
  exact proper_snc_model_actual_test_critical_prime_retention
    ρ hρ c f d e he D E cT ξ hinj hξ hsnc hsuppD hsuppE hE hcritical σ hσ cU ⟨x, hx⟩ hdisc


/-- OLD actual minimality is retained by the new pair. New minimality is a proved conclusion, never inferred from one non-klt component alone. -/
theorem minimal_lc_center_of_shared_snc_critical_index_containment
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d e : ℕ) (he : 1 ≤ e)
    (D E : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppD : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hsuppE : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (t : T) = 0)
    (hE : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) ≤ (e : ℤ))
    (hcritical : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) = (e : ℤ) →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    (hlcD : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z) :
    ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f e E V → V ≤ Z → V = Z := by
  intro V hV hVZ
  exact hmin V (logCanonicalCenter_of_shared_snc_critical_index_containment
    ρ hρ c f d e he D E cT ξ hinj hξ hsnc hsuppD hsuppE hE hcritical hlcD V hV) hVZ


/-- With the exact new non-klt locus, retained OLD minimality makes every actual new lc center equal to the SAME original center. -/
theorem isolated_lc_centers_unique_of_shared_snc_critical_index_containment
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d e : ℕ) (he : 1 ≤ e)
    (D E : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppD : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hsuppE : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (t : T) = 0)
    (hE : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) ≤ (e : ℤ))
    (hcritical : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) = (e : ℤ) →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    (hlcD : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f e E) ↔ x ∈ Z) :
    ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f e E V → V = Z := by
  intro V hV
  apply minimal_lc_center_of_shared_snc_critical_index_containment
    ρ hρ c f d e he D E cT ξ hinj hξ hsnc hsuppD hsuppE hE hcritical hlcD Z hmin V hV
  intro x hx
  exact (hNK x).mp (logPairIsLogCanonicalCenter_not_kltOverBasePoint c f e E V hV x hx)


/-- A divisor avoiding the retained isolated minimal center has ZERO pullback coefficient at EVERY actual new critical proper-test prime. -/
theorem isolated_retained_minimal_center_effective_avoidance_on_every_critical_prime
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d e : ℕ) (he : 1 ≤ e)
    (D E : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppD : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (hsuppE : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (t : T) = 0)
    (hE : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) ≤ (e : ℤ))
    (hcritical : ∀ i, cartierCoefficient (crepantBoundaryCartier ρ hρ c f e E cT etaleCharts_cover) (ξ i) = (e : ℤ) →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (ξ i) = (d : ℤ))
    (hlcD : LogPairIsLogCanonical c f d D) (Z : Closeds X)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f e E) ↔ x ∈ Z)
    (G : CartierDivisor X) (hG : G.IsEffective) (havoid : ¬ Z ≤ (effectiveCartierIdealSheaf G hG).support)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ X) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))] [IsProper σ]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (t : U) (ht : Order.coheight t = 1)
    (hnew : cartierCoefficient (logDiscrepancyDivisor n σ hσ c f e E cU etaleCharts_cover) t = -(e : ℤ)) :
    cartierCoefficient (cartierPullback σ G) t = 0 := by
  have hlcE : LogPairIsLogCanonical c f e E :=
    (logPairIsLogCanonical_iff_crepant_snc_coefficients ρ hρ c f e he E cT
      ξ hinj hξ hsnc hsuppE).mpr hE
  apply lc_center_avoidance_forces_critical_pullback_coefficient_zero
    σ hσ c f e E hlcE G hG ?_ cU t ht (by rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, hnew, neg_neg])
  intro V hV
  rw [isolated_lc_centers_unique_of_shared_snc_critical_index_containment
    ρ hρ c f d e he D E cT ξ hinj hξ hsnc hsuppD hsuppE hE hcritical hlcD Z hmin hNK V hV]
  exact havoid

end MixedFujita
