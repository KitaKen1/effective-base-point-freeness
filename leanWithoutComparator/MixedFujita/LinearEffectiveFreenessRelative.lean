/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeNumericalFreenessStatement
public import MixedFujita.KltAmplePerturbation
public import MixedFujita.SemiampleContractionProof

/-!
F2 from the base point free theorem and relative K-NF, without Ambro's canonical bundle formula
(step 17R).

Under the hypotheses of F2, the base point free theorem and the contraction of a semiample
divisor (§9.2) give, when κ(D) = k ≥ 1, a contraction f : X → Y onto a normal projective variety
of dimension k and an ample Cartier divisor H on Y with D = f*H + div ψ. The perturbation with an
ample remainder (`kltPair_exists_ample_remainder`) gives a klt pair (X, D₂/d₂) and w < d₂ a with
w D − D₂ ample. For m ≥ a + k + 1 put P = m H and L = c H with c = d₂ m − w > d₂(k + 1). Then
d₂ f*P − D₂ − f*L = (w D − D₂) − w div ψ is ample, and the numerical hypotheses hold for L on Y
as in §9.5. Relative K-NF makes m H globally generated, so
m D = f*(m H) + m div ψ is globally generated. For κ(D) = 0 the divisor D is principal.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- F2 from the base point free theorem for klt pairs and relative K-NF: Ambro's canonical
bundle formula is not used. -/
theorem linearEffectiveFreeness_of_basePointFree_of_relativeNumericalFreeness
    (hbpf : KltBasePointFreeStatement.{u}) (hrel : RelativeNumericalFreeness.{u}) :
    LinearEffectiveFreeness.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig k
    hk m hm
  obtain ⟨h0, hpos⟩ := nefContraction_of_basePointFree_of_semiampleContraction hbpf
    semiampleContractionStatement_holds K X n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D' heff hklt D hD
    a ha hnef hbig k hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · -- κ(D) = 0: D is principal
    obtain ⟨φ, hφ⟩ := h0 rfl
    obtain ⟨H₀, hH₀'⟩ := hH₀
    obtain ⟨p, -, hgg⟩ := cartierIsAmpleProj_exists_globallyGenerated_divisible_sequence H₀ hH₀'
    have hzero : CartierIsGloballyGenerated (0 : CartierDivisor X) := by
      simpa only [zero_mul, zero_smul] using hgg 0
    have h := cartierIsGloballyGenerated_add_principal (φ ^ m) hzero
    rwa [zero_add, principalCartierDivisor_power, ← hφ] at h
  · -- κ(D) ≥ 1: relative K-NF on the contraction
    obtain ⟨Y, _, _, _, _, f, _, _, H, ψ, hdimY, hnormY, hcovY, hfapp, hH, hDf⟩ := hpos hkpos
    obtain ⟨d₂, hd₂, D₂, w, heff₂, hklt₂, hw, hamp⟩ :=
      kltPair_exists_ample_remainder hdim hn hnorm hH₀ c₀ f₀ r hr D' heff hklt D a ha hnef hbig
    -- the arithmetic of c = d₂ m − w
    have h1 : d₂ * (a + k + 1) ≤ d₂ * m := Nat.mul_le_mul_left d₂ hm
    have h2 : d₂ * (a + k + 1) = d₂ * a + d₂ * (k + 1) := by ring
    have hgt : d₂ * (k + 1) < d₂ * m - w := by omega
    set c := d₂ * m - w with hcdef
    have hcw : d₂ * m = c + w := by omega
    have hc1 : 1 ≤ c := by omega
    have hL : CartierIsAmpleProj K (c • H) := cartierIsAmpleProj_nsmul hH hc1
    -- the positivity on X
    have hfH : cartierPullback f H = D - principalCartierDivisor X ψ := by
      rw [hDf]
      abel
    have hid : d₂ • cartierPullback f (m • H) - D₂ - cartierPullback f (c • H) =
        (w • D - D₂) + principalCartierDivisor X (ψ ^ w)⁻¹ := by
      rw [cartierPullback_nsmul, cartierPullback_nsmul, smul_smul, hcw, add_smul, hfH,
        principalCartierDivisor_inv, principalCartierDivisor_power]
      module
    have hrem : CartierIsAmpleProj K ((w • D - D₂) + principalCartierDivisor X (ψ ^ w)⁻¹) :=
      cartierIsAmpleProj_add_principal hamp _
    have hampX : CartierIsAmpleProj K
        (d₂ • cartierPullback f (m • H) - D₂ - cartierPullback f (c • H)) := by
      rw [hid]
      exact hrem
    -- the numerical hypotheses on Y
    have hG : c • H + principalCartierDivisor Y 1 = c • H := by
      rw [principalCartierDivisor_one, add_zero]
    have hcR : ((d₂ * (k + 1) : ℕ) : ℝ) < (c : ℝ) := by exact_mod_cast hgt
    have hcR0 : (0 : ℝ) ≤ ((d₂ * (k + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hvol : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
        ((((d₂ * (k + 1) : ℕ) : ℝ) ^ k + δ) * (j : ℝ) ^ k / k.factorial ≤
          cartierRestrictedDim K (j • (c • H)) (genericPoint Y)) := by
      have hpow : ((d₂ * (k + 1) : ℕ) : ℝ) ^ k < (c : ℝ) ^ k :=
        pow_lt_pow_left₀ hcR hcR0 (by omega)
      set δ := ((c : ℝ) ^ k - ((d₂ * (k + 1) : ℕ) : ℝ) ^ k) / 2 with hδ
      have hδ0 : 0 < δ := by rw [hδ]; linarith
      refine ⟨δ, hδ0, ?_⟩
      filter_upwards [ample_nsmul_restrictedDim_eventually hdimY hkpos hH hc1 _ 1 hG
        (genericPoint Y) (topologicalKrullDim_closure_genericPoint hdimY) hkpos hδ0] with j hj
      refine le_trans (le_of_eq ?_) hj
      congr 2
      rw [hδ]
      ring
    have hsub : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
        d < k → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
          ((((d₂ * (k + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedDim K (j • (c • H)) η) := by
      intro η d hd hd1 _ ε hε
      have hpow : ((d₂ * (k + 1) : ℕ) : ℝ) ^ d ≤ (c : ℝ) ^ d := pow_le_pow_left₀ hcR0 hcR.le d
      filter_upwards [ample_nsmul_restrictedDim_eventually hdimY hkpos hH hc1 _ 1 hG η hd hd1 hε]
        with j hj
      refine le_trans ?_ hj
      have hj0 : (0 : ℝ) ≤ (j : ℝ) ^ d / d.factorial := by positivity
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hj0
    have hgen : CartierIsGloballyGenerated (m • H) :=
      hrel K X n hdim hn hnorm hcov hH₀ c₀ f₀ d₂ hd₂ D₂ heff₂ hklt₂ Y k hdimY hkpos hnormY hcovY
        f hfapp (m • H) (c • H) hL hampX hvol hsub
    rw [hDf, smul_add, ← cartierPullback_nsmul, ← principalCartierDivisor_power]
    exact cartierIsGloballyGenerated_add_principal _
      (cartierIsGloballyGenerated_cartierPullback f _ hgen)

end MixedFujita
