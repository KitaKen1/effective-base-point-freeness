/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothPairRealizationClosedness
public import MixedFujita.KltClosedPointMinimizer
public import MixedFujita.KltNumericalFreenessConditional
public import MixedFujita.LinearEffectiveFreenessAmple
public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.NormalHartogs
public import MixedFujita.LocalIdealRealization
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.ProperBirationalSections
public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.KodairaLemmaNormal
public import MixedFujita.KltPerturbationNefAmple
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.ProjectiveCurveCohomology

/-!
K-NF for smooth varieties, and F2 for an ample divisor on a smooth variety (step 15).

For a klt pair with effective boundary on a smooth projective variety, the two closedness
hypotheses of K-NF hold (checks 560, 561); with Kawamata–Viehweg vanishing (check 558) the
minimizer data exist at every closed point where P is not generated, and §6 gives the global
generation (`kawamataNumericalFreeness_of_smooth`). The boundary is effective as a Cartier
divisor because its coefficients at the codimension-one points are nonnegative and the stalks
are normal (`pairBoundaryCartier_isEffective`, by Hartogs; at a codimension-one point a rational
function of nonnegative order is regular, `mem_range_stalk_of_ord_nonneg`).

The argument of check 166 for F2 with D ample uses K-NF only on X itself, with the perturbed klt
pair of §9.3; so F2 holds for an ample divisor on a smooth projective variety
(`linearEffectiveFreenessAmple_of_smooth`): m D is globally generated for m ≥ a + κ(D) + 1.
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

section Hartogs

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]

/-- At a codimension-one point with normal stalk, a nonzero rational function of nonnegative
order is regular. -/
theorem mem_range_stalk_of_ord_nonneg (hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (ξ : Y) (hξ : Order.coheight ξ = 1) (f : Y.functionFieldˣ)
    (hf : 0 ≤ Y.ord (f : Y.functionField) ξ) :
    (f : Y.functionField) ∈ (algebraMap (Y.presheaf.stalk ξ) Y.functionField).range := by
  have := hnorm ξ
  have : IsDiscreteValuationRing (Y.presheaf.stalk ξ) := normal_codimensionOne_stalk_DVR ⟨ξ, hξ⟩
  have : ValuationRing (Y.presheaf.stalk ξ) := valuationRing_stalk_of_coheight_eq_one ξ hξ
  rcases ValuationRing.isInteger_or_isInteger (Y.presheaf.stalk ξ) (f : Y.functionField) with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨a, ha⟩
  · by_cases hbu : IsUnit b
    · refine ⟨((hbu.unit⁻¹ : (Y.presheaf.stalk ξ)ˣ) : Y.presheaf.stalk ξ), ?_⟩
      have h1 : algebraMap (Y.presheaf.stalk ξ) Y.functionField
          ((hbu.unit⁻¹ : (Y.presheaf.stalk ξ)ˣ) : Y.presheaf.stalk ξ) *
          algebraMap (Y.presheaf.stalk ξ) Y.functionField b = 1 := by
        rw [← map_mul, IsUnit.val_inv_mul, map_one]
      rw [hb] at h1
      have hf0 : (f : Y.functionField) ≠ 0 := Units.ne_zero f
      field_simp at h1
      exact h1
    · exfalso
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [map_zero] at hb
        exact inv_ne_zero (Units.ne_zero f) hb.symm
      have hbm : b ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk ξ) :=
        (IsLocalRing.mem_maximalIdeal _).mpr hbu
      have h1 := (mem_maximalIdeal_pow_ceil_iff_primeOrder (Y := Y) ⟨ξ, hξ⟩ b 1).mp
        (by simpa using hbm) hb0
      rw [hb, Scheme.ord_inv] at h1
      have h2 : ((Y.ord (f : Y.functionField) ξ : ℤ) : ℝ) ≥ 0 := by exact_mod_cast hf
      push_cast at h1
      linarith

end Hartogs

section Boundary

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- **The boundary of a pair with effective boundary on a smooth variety is an effective Cartier
divisor.** -/
theorem pairBoundaryCartier_isEffective (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ : CartierDivisor Y) (heff : LogPairBoundaryEffective cY fY d D₀) :
    (pairBoundaryCartier cY fY d D₀).IsEffective := by
  have hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun y =>
    smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n) y
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro x
  obtain ⟨f, hf⟩ := (pairBoundaryCartier cY fY d D₀).exists_isLocalEquationAt x
  refine ⟨f, hf, ?_⟩
  obtain ⟨W, hxW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  apply mem_range_stalk_of_codimOne hnorm x W hxW
  intro ξ hξW hξ
  have hfξ : (pairBoundaryCartier cY fY d D₀).IsLocalEquationAt ξ f :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hW hξW
  apply mem_range_stalk_of_ord_nonneg hnorm ξ hξ f
  rw [← cartierCoefficient_eq_ord hfξ]
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K Y n, ξ ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top ξ)
  have h1 := heff c ξ hc hξ
  unfold pairBoundaryCartier smoothCanonicalDivisor
  rw [cartierCoefficient_sub, cartierCoefficient_nsmul, cartierCoefficient_add,
    cartierCoefficient_eq_ord (canonicalDivisor_isLocalEquationAt cY etaleCharts_cover c hc),
    cartierCoefficient_eq_ord (CartierDivisor.isLocalEquationAt_principalCartierDivisor ξ fY)]
  rw [Units.val_mul, Y.ord_mul (Units.ne_zero _) (Units.ne_zero _)] at h1
  linarith [mul_add (d : ℤ) (Y.ord (fY : Y.functionField) ξ)
      (Y.ord ((etaleChartCanonicalEquation cY c : Y.functionFieldˣ) : Y.functionField) ξ),
    mul_add (d : ℤ) (Y.ord ((etaleChartCanonicalEquation cY c : Y.functionFieldˣ) :
      Y.functionField) ξ) (Y.ord (fY : Y.functionField) ξ)]

end Boundary

section Freeness

/-- **K-NF for smooth varieties**: for a projective klt pair (Y, B) with effective boundary on a
smooth variety of dimension n ≥ 1 over an uncountable algebraically closed field of
characteristic zero, and a Cartier divisor P with A = P − (K_Y + B) ample, A^n > (n + 1)^n and
A^d · W ≥ (n + 1)^d for every proper positive-dimensional subvariety W, P is globally generated. -/
theorem kawamataNumericalFreeness_of_smooth (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    [Uncountable K] (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] (hn : 1 ≤ n)
    (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r) (D : CartierDivisor Y)
    (heff : LogPairBoundaryEffective c₀ f₀ r D) (hklt : LogPairIsKlt c₀ f₀ r D)
    (P : CartierDivisor Y) (hA : CartierIsAmpleProj K (r • P - D))
    (hvol : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
      ((((r * (n + 1) : ℕ) : ℝ) ^ n + δ) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • (r • P - D)) (genericPoint Y)))
    (hsub : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d → d < n →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((((r * (n + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedDim K (j • (r • P - D)) η)) :
    CartierIsGloballyGenerated P := by
  have hnorm : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun y =>
    smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n) y
  have hcov : CodimOneChartCovered n K Y := fun ξ _ =>
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := Y) (n := n)).symm ▸ Opens.mem_top ξ)
  obtain ⟨m, hm, v, e, hcl, he, -⟩ := id hA
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of K))
  have hE := pairBoundaryCartier_isEffective c₀ f₀ r D heff
  exact klt_cartierIsGloballyGenerated_of_minimizerData (kawamataViehwegVanishingSNC_of_charZero K n)
    hn hnorm hcov c₀ f₀ r hr D heff hklt P hA
    (fun m₀ hm₀ x hx _ => klt_ample_minimizerData_of_knf_numerical_and_closedPoints hn c₀ f₀ r hr
      D (r • P - D) hklt hA hvol hsub x hx
      (Filter.Eventually.of_forall fun j =>
        realizationSetsZariskiClosed_pair c₀ f₀ hr D hklt hE x hx (j • (r • P - D)))
      (closedPointRealization_pair c₀ f₀ hr D hklt hE (r • P - D)) m₀ hm₀)

/-- **F2 for an ample divisor on a smooth projective variety**: for a projective klt pair (X, Δ)
with effective boundary on a smooth variety, an ample Cartier divisor D and a ≥ 1 with
a D − (K_X + Δ) nef and big, m D is globally generated for every m ≥ a + κ(D) + 1. -/
theorem linearEffectiveFreenessAmple_of_smooth (K : Type u) [Field K] [IsAlgClosed K]
    [CharZero K] [Uncountable K] (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hH₀ : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsAmpleProj K D)
    (a : ℕ) (ha : 1 ≤ a) (hnef : CartierIsNef K ((r * a) • D - D'))
    (hbig : CartierIsBig K ((r * a) • D - D')) (k : ℕ) (hk : CartierIitakaDimension K D k)
    (m : ℕ) (hm : a + k + 1 ≤ m) : CartierIsGloballyGenerated (m • D) := by
  have hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun x =>
    smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n) x
  have hcov : CodimOneChartCovered n K X := fun ξ _ =>
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := n)).symm ▸ Opens.mem_top ξ)
  have hkn : k = n := eq_of_iitakaDimension_of_isAmpleProj hdim hn hD hk
  rw [hkn] at hm
  obtain ⟨f₁, rY, hrY, DY, u, φ, heffY, hkltY, hDY, hu⟩ :=
    kodairaPerturbation_of_kltPerturbation (kltPerturbation_of_nefAddAmple nefAddAmpleStatement_holds)
      K X n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D a ha hnef hbig
  have h1 : rY * (a + n + 1) ≤ rY * m := Nat.mul_le_mul_left rY hm
  have h2 : rY * (a + n + 1) = rY * a + rY * (n + 1) := by ring
  have hgt : rY * (n + 1) < rY * m - u := by omega
  set c := rY * m - u with hcdef
  have hcu : rY * m = c + u := by omega
  have hc1 : 1 ≤ c := by omega
  have hG : rY • (m • D) - DY + principalCartierDivisor X φ = c • D := by
    rw [hDY, smul_smul, hcu, add_smul]
    abel
  have hGeq : rY • (m • D) - DY = c • D + principalCartierDivisor X φ⁻¹ := by
    rw [principalCartierDivisor_inv, ← hG]
    abel
  have hample : CartierIsAmpleProj K (rY • (m • D) - DY) := by
    rw [hGeq]
    exact cartierIsAmpleProj_add_principal (cartierIsAmpleProj_nsmul hD hc1) _
  have hcR : ((rY * (n + 1) : ℕ) : ℝ) < (c : ℝ) := by exact_mod_cast hgt
  have hcR0 : (0 : ℝ) ≤ ((rY * (n + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hvol : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
      ((((rY * (n + 1) : ℕ) : ℝ) ^ n + δ) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • (rY • (m • D) - DY)) (genericPoint X)) := by
    have hpow : ((rY * (n + 1) : ℕ) : ℝ) ^ n < (c : ℝ) ^ n := pow_lt_pow_left₀ hcR hcR0 (by omega)
    set δ := ((c : ℝ) ^ n - ((rY * (n + 1) : ℕ) : ℝ) ^ n) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    refine ⟨δ, hδ0, ?_⟩
    filter_upwards [ample_nsmul_restrictedDim_eventually hdim hn hD hc1 _ φ hG
      (genericPoint X) (topologicalKrullDim_closure_genericPoint hdim) hn hδ0] with j hj
    refine le_trans (le_of_eq ?_) hj
    congr 2
    rw [hδ]
    ring
  have hsub : ∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
      d < n → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((((rY * (n + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedDim K (j • (rY • (m • D) - DY)) η) := by
    intro η d hd hd1 _ ε hε
    have hpow : ((rY * (n + 1) : ℕ) : ℝ) ^ d ≤ (c : ℝ) ^ d := pow_le_pow_left₀ hcR0 hcR.le d
    filter_upwards [ample_nsmul_restrictedDim_eventually hdim hn hD hc1 _ φ hG η hd hd1 hε]
      with j hj
    refine le_trans ?_ hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) ^ d / d.factorial := by positivity
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hj0
  exact kawamataNumericalFreeness_of_smooth K X n hn c₀ f₁ rY hrY DY heffY hkltY (m • D) hample
    hvol hsub

end Freeness

end MixedFujita
