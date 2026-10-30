/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KodairaLemmaNormal

/-!
An actual nef and big Cartier class M/q admits an effective representative
preserving a supplied sub-klt pair. Kodaira's lemma supplies a fixed effective
divisor, a sufficiently small coefficient preserves klt, and the remaining
nef-plus-ample class is cut by existing rational ample Bertini. The boundary
of the supplied pair need not be effective. Nef-plus-ample ampleness remains
an explicit input; positivity of M is not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- The ample remainder and the small fixed part reconstruct M/q exactly. -/
theorem nefBig_perturbation_remainder_identity (M H P : CartierDivisor X)
    (k q e : ℕ) :
    q • (k • M - H + P) + ((e + 1) • M + q • H) =
      (k * q + e + 1) • M + q • P := by
  module

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- Construct an effective representative of M/q preserving all-model klt,
including an exact Cartier identity with an actual principal witness. -/
theorem logPairIsKlt_exists_effective_nefBig_representative
    (hna : NefAddAmpleStatement.{u})
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (M H : CartierDivisor X) (hMnef : CartierIsNef K M) (hMbig : CartierIsBig K M)
    (hH : CartierIsAmpleProj K H) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (t : ℕ) (_ : 1 ≤ t) (G : CartierDivisor X) (χ : X.functionFieldˣ),
      G.IsEffective ∧ LogPairIsKlt c f (t * d) (t • D + G) ∧
      q • G = (t * d) • M + principalCartierDivisor X χ := by
  obtain ⟨k, hk, s₀, hs₀⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj
    hdim hn hnorm c M H hMbig hH
  let G₀ := cartierSectionZeroDivisor (k • M - H) s₀ hs₀
  let σ := cartierSectionUnit (k • M - H) s₀ hs₀
  have hG₀ : G₀.IsEffective := cartierSectionZeroDivisor_isEffective _ s₀ hs₀
  have hpos : (0 : ℚ) < (((k * q) * d : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  obtain ⟨j, hj, -, hsmall, hklt₁⟩ :=
    logPairIsKlt_exists_small_fixed_divisor_perturbation c f d hd D (d • G₀) hklt
      (1 / (((k * q) * d : ℕ) : ℚ)) (one_div_pos.mpr hpos)
  have hjd : (0 : ℚ) < ((j * d : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hlt : (k * q) * d < j * d := by
    exact_mod_cast (one_div_lt_one_div hjd hpos).mp hsmall
  have hkj : k * q < j := Nat.lt_of_mul_lt_mul_right hlt
  obtain ⟨e, rfl⟩ : ∃ e, j = k * q + e + 1 := ⟨j - k * q - 1, by omega⟩
  let j := k * q + e + 1
  let A := (e + 1) • M + q • H
  have hA : CartierIsAmpleProj K A :=
    hna K X _ _ (cartierIsNef_nsmul hMnef (e + 1)) (cartierIsAmpleProj_nsmul hH hq)
  obtain ⟨m, r, s, hs, hm, -, hcommon, -, -, -, -, hklt₂, -, -⟩ :=
    logPairIsKlt_exists_rational_ample_perturbation hnorm c f (j * d)
      (Nat.mul_pos (by dsimp [j]; omega) (by omega)) (j • D + d • G₀) hklt₁
      A hA (j * q) (Nat.mul_pos (by dsimp [j]; omega) (by omega)) 0 1 one_pos
      ∅ Set.finite_empty
  have hcancel : r * q = m * d := by
    apply mul_left_cancel₀ (by dsimp [j]; omega : j ≠ 0)
    calc j * (r * q) = r * (j * q) := by ring
      _ = m * (j * d) := hcommon.symm
      _ = j * (m * d) := by ring
  let τ := cartierSectionUnit (r • A) s hs
  let G := m • (d • G₀) + cartierSectionZeroDivisor (r • A) s hs
  have hmult : ∀ a : ℕ, (a • G₀).IsEffective := by
    intro a
    induction a with
    | zero => simpa only [zero_smul] using (CartierDivisor.isEffective_zero (X := X))
    | succ a ha => simpa only [succ_nsmul] using ha.add hG₀
  have hG : G.IsEffective := by
    apply CartierDivisor.IsEffective.add _ (cartierSectionZeroDivisor_isEffective _ s hs)
    simpa only [smul_smul] using hmult (m * d)
  refine ⟨m * j, Nat.mul_pos (by omega) (by dsimp [j]; omega), G,
    σ ^ (m * d * q) * τ ^ q, hG, ?_, ?_⟩
  · simpa only [G, nsmul_add, smul_smul, Nat.mul_assoc, add_assoc] using hklt₂
  · have hid : q • G₀ + A = j • M + q • principalCartierDivisor X σ :=
      nefBig_perturbation_remainder_identity M H (principalCartierDivisor X σ) k q e
    dsimp only [G]
    rw [nsmul_add, cartierSectionZeroDivisor, nsmul_add]
    have hsec : q • (r • A) = (m * d) • A := by
      simp only [smul_smul, Nat.mul_comm q r, hcancel]
    rw [hsec]
    simp only [principalCartierDivisor_mul, principalCartierDivisor_power]
    rw [← add_assoc]
    calc q • (m • (d • G₀)) + (m * d) • A + q • principalCartierDivisor X τ =
        (m * d) • (q • G₀ + A) + q • principalCartierDivisor X τ := by module
      _ = (m * d) • (j • M + q • principalCartierDivisor X σ) +
          q • principalCartierDivisor X τ := by rw [hid]
      _ = _ := by module

end MixedFujita
