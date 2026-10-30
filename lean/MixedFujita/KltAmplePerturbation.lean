/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltPerturbationNefAmple
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.KodairaLemmaStatementProof
public import MixedFujita.LinearEffectiveFreenessReduction

/-!
The perturbation of §9.3 with an ample remainder (step 17R).

Relative K-NF uses the Kawamata–Viehweg theorem on X, so the perturbed pair must keep an ample
part of a D − (K_X + Δ) instead of absorbing it into a general member. Let (X, Δ) be a projective
klt pair with effective boundary, D' = r(K_X + Δ), and T₀ = a D − (K_X + Δ) nef and big. As in
`kltPerturbation_of_nefAddAmple`:

* Kodaira's lemma gives a nonzero section of m r T₀ − H for an ample H, with zero divisor G;
* the coefficient 1/(m₁ r) of G keeps the pair klt, with m₁ = m + e + 1 and
  D₁ = m₁ D' + G of index d₁ = m₁ r;
* B = (e + 1) r T₀ + H is ample (nef plus ample), and A' = k B − D is ample for large k.

Then d₁ a D − D₁ = B − div σ, so with d₂ = k d₁, D₂ = k D₁ and w = k d₁ a − 1 one has
w D − D₂ = A' − k div σ, which is ample, and w < d₂ a: the pair (X, D₂/d₂ − K_X) is klt with
K_X + Δ₂ ∼_ℚ (a − 1/d₂) D − A'/d₂.
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

/-- The divisor identity of the ample remainder: with k d₁ a = t + 1, d₁ = (m + e + 1) r and
D₁ = (m + e + 1) D' + (m (r a D − D') − H + P), one has
t D − k D₁ = (−D + k ((e + 1)(r a D − D') + H)) − k P. -/
theorem ample_remainder_divisor_identity {X : Scheme.{u}} [IsIntegral X]
    (D D' H P : CartierDivisor X) (m e r a k t : ℕ) (ht : k * ((m + e + 1) * r) * a = t + 1) :
    t • D - k • ((m + e + 1) • D' + (m • ((r * a) • D - D') - H + P)) =
      (-D + k • ((e + 1) • ((r * a) • D - D') + H)) - k • P := by
  have htD : t • D = (k * ((m + e + 1) * r) * a) • D - D := by
    rw [ht, add_smul, one_smul]
    abel
  rw [htD]
  module

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

/-- The perturbation of §9.3 with an ample remainder: on a normal projective klt pair (X, Δ) with
effective boundary, r(K_X + Δ) = D', and a D − (K_X + Δ) nef and big, there are a klt pair
(X, Δ₂) with effective boundary, d₂(K_X + Δ₂) = D₂, and a natural number w < d₂ a with w D − D₂
ample. -/
theorem kltPair_exists_ample_remainder (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hH₀ : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (a : ℕ) (ha : 1 ≤ a)
    (hnef : CartierIsNef K ((r * a) • D - D')) (hbig : CartierIsBig K ((r * a) • D - D')) :
    ∃ (d₂ : ℕ) (_ : 1 ≤ d₂) (D₂ : CartierDivisor X) (w : ℕ),
      LogPairBoundaryEffective c₀ f₀ d₂ D₂ ∧ LogPairIsKlt c₀ f₀ d₂ D₂ ∧ w < d₂ * a ∧
      CartierIsAmpleProj K (w • D - D₂) := by
  obtain ⟨H, hH⟩ := hH₀
  obtain ⟨-, -, N₀, e₀, he₀, hbase₀, -⟩ := id hH
  have : IsProper (X ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e₀ hbase₀
  obtain ⟨m, hm, s, hs⟩ :=
    kodairaLemmaStatement_holds K X n hdim hn hnorm ⟨H, hH⟩ ((r * a) • D - D') H hbig hH
  have hGeff := cartierSectionZeroDivisor_isEffective _ s hs
  have hmr : (0 : ℚ) < ((m * r : ℕ) : ℚ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  obtain ⟨m₁, hm₁, -, hsmall, heff₁, hklt₁⟩ :=
    logPairIsKlt_exists_small_fixed_effective_divisor_perturbation c₀ f₀ r hr D'
      (cartierSectionZeroDivisor _ s hs) hklt heff hGeff (1 / ((m * r : ℕ) : ℚ))
      (one_div_pos.mpr hmr)
  have hm₁r : (0 : ℚ) < ((m₁ * r : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hlt : m * r < m₁ * r := by
    have := (one_div_lt_one_div hm₁r hmr).mp hsmall
    exact_mod_cast this
  have hmm₁ : m < m₁ := Nat.lt_of_mul_lt_mul_right hlt
  obtain ⟨e, rfl⟩ : ∃ e, m₁ = m + e + 1 := ⟨m₁ - m - 1, by omega⟩
  have hB : CartierIsAmpleProj K ((e + 1) • ((r * a) • D - D') + H) :=
    nefAddAmpleStatement_holds K X _ H (cartierIsNef_nsmul hnef (e + 1)) hH
  obtain ⟨j₀, hj₀⟩ := cartierIsAmpleProj_eventually_twist_veryAmple hB (-D)
  have hA' : CartierIsAmpleProj K (-D + (j₀ + 1) • ((e + 1) • ((r * a) • D - D') + H)) :=
    cartierIsAmpleProj_of_veryAmple (hj₀ (j₀ + 1) (by omega))
  have hk : 1 ≤ j₀ + 1 := by omega
  have hd₁ : 1 ≤ (m + e + 1) * r := Nat.mul_pos (by omega) (by omega)
  have hpos : 1 ≤ (j₀ + 1) * ((m + e + 1) * r) * a :=
    Nat.mul_pos (Nat.mul_pos hk hd₁) (by omega)
  obtain ⟨t, ht⟩ : ∃ t, (j₀ + 1) * ((m + e + 1) * r) * a = t + 1 :=
    ⟨_, (Nat.sub_add_cancel hpos).symm⟩
  set σ := cartierSectionUnit (m • ((r * a) • D - D') - H) s hs with hσ
  refine ⟨(j₀ + 1) * ((m + e + 1) * r), Nat.mul_pos hk hd₁,
    (j₀ + 1) • ((m + e + 1) • D' + cartierSectionZeroDivisor _ s hs), t,
    (logPairBoundaryEffective_scale_denominator_iff c₀ f₀ _ (j₀ + 1) hk _).mpr heff₁,
    (logPairIsKlt_scale_denominator_iff c₀ f₀ _ (j₀ + 1) hk _).mpr hklt₁, ?_, ?_⟩
  · rw [ht]
    exact Nat.lt_add_one t
  · have hid := ample_remainder_divisor_identity D D' H (principalCartierDivisor X σ) m e r a
      (j₀ + 1) t ht
    have hzero : cartierSectionZeroDivisor (m • ((r * a) • D - D') - H) s hs =
        m • ((r * a) • D - D') - H + principalCartierDivisor X σ := rfl
    have hfin : t • D - (j₀ + 1) • ((m + e + 1) • D' + cartierSectionZeroDivisor _ s hs) =
        (-D + (j₀ + 1) • ((e + 1) • ((r * a) • D - D') + H)) +
          principalCartierDivisor X (σ ^ (j₀ + 1))⁻¹ := by
      rw [hzero, hid, principalCartierDivisor_inv, principalCartierDivisor_power]
      abel
    rw [hfin]
    exact cartierIsAmpleProj_add_principal hA' _

end MixedFujita
