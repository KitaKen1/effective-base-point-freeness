/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SNCWeightTestPrimes
public import MixedFujita.SNCLogCanonicalDiscrepancyBound

/-! SNC discrepancy等号条件による旧臨界性保持。 check-275：元のlc臨界係数から選択成分を内部抽出し、通常H1型KVを明示した元の孤立lc構成の同じ実切断へ全開関数貼合せ・成分正規性・全交差被約性を接続。SNC discrepancy等号条件から新臨界素因子が旧臨界素因子であることを証明し、全双有理テストの比較と孤立化後の最小性保持を内部化。任意分母kltアンカーを含む元の最小lc中心の孤立化で、全lc中心＝元中心を内部構成。有効Cartier分離と正のlc閾値により、非固有な滑らかな双有理テストの臨界素因子の中心も正確に一致。指示重みの抽出素因子から、一意な孤立lc対の全臨界SNC交差の各極大一般化点が同じ中心を支配することを証明。 -/

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


/-- Equality in the actual SNC discrepancy bound propagates criticality:
if every NEW critical coordinate is OLD critical, a new discrepancy -e
forces old discrepancy -d. No uniform deficit-comparison constant is needed. -/
theorem snc_integer_critical_discrepancy_retention
    {ι : Type v} [Fintype ι] (d e : ℕ) (he : 1 ≤ e) (J : ℤ)
    (v b c : ι → ℤ) (hv : ∀ i, 0 ≤ v i)
    (hsum : ∑ i, v i ≤ 1 + J)
    (hc : ∀ i, c i ≤ (e : ℤ))
    (hcritical : ∀ i, c i = (e : ℤ) → b i = (d : ℤ))
    (hnew : (e : ℤ) * J - ∑ i, c i * v i = -(e : ℤ)) :
    (d : ℤ) * J - ∑ i, b i * v i = -(d : ℤ) := by
  classical
  let W : ℤ := 1 + J - ∑ i, v i
  have hW : 0 ≤ W := by dsimp only [W]; omega
  have hepos : (0 : ℤ) < e := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one he)
  have hterm (i : ι) : 0 ≤ ((e : ℤ) - c i) * v i :=
    mul_nonneg (sub_nonneg.mpr (hc i)) (hv i)
  have htotal : (e : ℤ) * W + ∑ i, ((e : ℤ) - c i) * v i = 0 := by
    dsimp only [W]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    nlinarith [hnew]
  have hsum0 : ∑ i, ((e : ℤ) - c i) * v i = 0 := by
    have hsnon := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hterm i)
    have heW := mul_nonneg hepos.le hW
    omega
  have hWzero : W = 0 := by nlinarith [htotal]
  have hterm0 (i : ι) : ((e : ℤ) - c i) * v i = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hterm j)).mp hsum0 i
      (Finset.mem_univ i)
  have hold0 : ∑ i, ((d : ℤ) - b i) * v i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : v i = 0
    · simp only [hi, mul_zero]
    · have hci : c i = (e : ℤ) := by
        have h := (mul_eq_zero.mp (hterm0 i)).resolve_right hi
        omega
      rw [hcritical i hci, sub_self, zero_mul]
  have holdsplit : (d : ℤ) * J - ∑ i, b i * v i + (d : ℤ) =
      (d : ℤ) * W + ∑ i, ((d : ℤ) - b i) * v i := by
    dsimp only [W]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hWzero, hold0, mul_zero, add_zero] at holdsplit
  omega


/-- The exact actual discrepancy formula on a FIXED SNC chart. This
allows two different boundaries to use the same actual coordinate orders
and the same Jacobian, instead of assuming a comparison of test values. -/
theorem normal_isSNCChart_actual_discrepancy_formula_at_prime
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (B : CartierDivisor X)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsupp : ∀ x : CodimensionOnePoint X, (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T)
    (c : EtaleChart K X n) (τ : Fin r → Option (Fin n))
    (hc : ρ (t : T) ∈ c.U) (hchart : IsSNCChart c ξ τ)
    (c' : EtaleChart K T n) (ht : (t : T) ∈ c'.U) :
    cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      cT etaleCharts_cover) (t : T) =
      (d : ℤ) * T.ord (chartRelativeJacobianDet ρ c c') (t : T) -
        ∑ i, cartierCoefficient B (ξ i) * T.ord ((dominantFunctionFieldMap ρ).hom
          (sncChartComponentEquation c τ i : X.functionField)) (t : T) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    fun x => smoothOverField_codimensionOne_stalk_DVR (K := K) x
  obtain ⟨f, hf, a, ha⟩ := normal_isSNCChart_boundary_local_product hnorm B c ξ hinj hξ τ hchart hsupp
    (ρ (t : T)) hc
  rw [logDiscrepancyDivisor_boundary_add, cartierCoefficient_sub, cartierCoefficient_nsmul,
    cartierPullback_coefficient_of_local_product ρ B t f hf a _ _ ha]
  have hloc := relativeCanonicalDivisor_isLocalEquationAt ρ c₀ etaleCharts_cover cT etaleCharts_cover
    (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ cT) (t : T) c hc c' ht
  unfold birationalRelativeCanonicalDivisor
  rw [cartierCoefficient_eq_ord hloc, IsUnit.unit_spec]


/-- Containment of critical coordinate indices propagates to EVERY
actual smooth birational prime. The test morphism need NOT be proper.
The equality case of the SNC Jacobian bound supplies the propagation. -/
theorem isSNCFamily_actual_critical_prime_retention
    {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
    [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d e : ℕ) (he : 1 ≤ e)
    (B C : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsuppB : ∀ x : CodimensionOnePoint X, (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (hsuppC : ∀ x : CodimensionOnePoint X, (x : X) ∉ Set.range ξ → cartierCoefficient C (x : X) = 0)
    (hC : ∀ i, cartierCoefficient C (ξ i) ≤ (e : ℤ))
    (hcritical : ∀ i, cartierCoefficient C (ξ i) = (e : ℤ) → cartierCoefficient B (ξ i) = (d : ℤ))
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T)
    (hnew : cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ e
      (e • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + C)
      cT etaleCharts_cover) (t : T) = -(e : ℤ)) :
    cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
      cT etaleCharts_cover) (t : T) = -(d : ℤ) := by
  let : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc x
  obtain ⟨c, τ, hc, hchart⟩ := hsnc (ρ (t : T))
  obtain ⟨c', ht⟩ : ∃ c' : EtaleChart K T n, (t : T) ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸ Opens.mem_top (t : T))
  rw [normal_isSNCChart_actual_discrepancy_formula_at_prime ρ hρ hnorm c₀ f₀ e C
    ξ hinj hξ hsuppC cT t c τ hc hchart c' ht] at hnew
  rw [normal_isSNCChart_actual_discrepancy_formula_at_prime ρ hρ hnorm c₀ f₀ d B
    ξ hinj hξ hsuppB cT t c τ hc hchart c' ht]
  exact snc_integer_critical_discrepancy_retention d e he _ _
    (fun i => cartierCoefficient B (ξ i)) (fun i => cartierCoefficient C (ξ i))
    (fun i => sncChartComponentEquation_pullback_ord_nonneg ρ c τ (t : T) hc i)
    (actual_snc_coordinate_sum_le_jacobian ρ hρ t c hc ξ τ hchart c' ht) hC hcritical hnew

end MixedFujita
