/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NefBigKltRepresentative
public import MixedFujita.RationalPullbackAmpleKltPerturbation
public import MixedFujita.NormalEffectiveCartierPrime

/-!
Construct an effective klt representative of the pullback of a nef-big class
on another normal projective variety. Kodaira decomposition is performed on
that variety; only its fixed effective part is pulled back before the small
klt perturbation. The ample remainder supplies globally generated pulled
multiples, without requiring the pullback itself to be big or ample.
Nef-plus-ample ampleness remains an explicit input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n k : ℕ}
  {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of K))]

/-- A dominant pullback of M/q has an effective klt representative even when
the pulled divisor is not big on the source. -/
theorem logPairIsKlt_exists_effective_nefBig_pullback_representative
    (h : X ⟶ Z) [IsDominant h] (hna : NefAddAmpleStatement.{u})
    (hdimZ : topologicalKrullDim Z = k) (hk : 1 ≤ k)
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (cZ : EtaleChart K Z k) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (M H : CartierDivisor Z) (hMnef : CartierIsNef K M) (hMbig : CartierIsBig K M)
    (hH : CartierIsAmpleProj K H) (q : ℕ) (hq : 1 ≤ q) :
    ∃ (t : ℕ) (_ : 1 ≤ t) (G : CartierDivisor X) (χ : X.functionFieldˣ),
      G.IsEffective ∧ LogPairIsKlt c f (t * d) (t • D + G) ∧
      q • G = (t * d) • cartierPullback h M + principalCartierDivisor X χ := by
  obtain ⟨a, ha, s₀, hs₀⟩ := exists_section_nsmul_sub_of_isBig_of_isAmpleProj
    hdimZ hk hnormZ cZ M H hMbig hH
  let GZ := cartierSectionZeroDivisor (a • M - H) s₀ hs₀
  let G₀ := cartierPullback h GZ
  let σZ := cartierSectionUnit (a • M - H) s₀ hs₀
  let σ := Units.map (dominantFunctionFieldMap h).hom.toMonoidHom σZ
  have hG₀ : G₀.IsEffective := cartierPullback_effective_of_effective h GZ
    (cartierSectionZeroDivisor_isEffective _ s₀ hs₀)
  have hpos : (0 : ℚ) < (((a * q) * d : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  obtain ⟨j, hj, -, hsmall, hklt₁⟩ :=
    logPairIsKlt_exists_small_fixed_divisor_perturbation c f d hd D (d • G₀) hklt
      (1 / (((a * q) * d : ℕ) : ℚ)) (one_div_pos.mpr hpos)
  have hjd : (0 : ℚ) < ((j * d : ℕ) : ℚ) := by
    exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hlt : (a * q) * d < j * d := by
    exact_mod_cast (one_div_lt_one_div hjd hpos).mp hsmall
  have haj : a * q < j := Nat.lt_of_mul_lt_mul_right hlt
  obtain ⟨e, rfl⟩ : ∃ e, j = a * q + e + 1 := ⟨j - a * q - 1, by omega⟩
  let j := a * q + e + 1
  let A := (e + 1) • M + q • H
  have hA : CartierIsAmpleProj K A :=
    hna K Z _ _ (cartierIsNef_nsmul hMnef (e + 1)) (cartierIsAmpleProj_nsmul hH hq)
  obtain ⟨m, r, s, hs, hm, -, hcommon, -, -, -, -, hklt₂, -, -⟩ :=
    logPairIsKlt_exists_rational_pullback_ample_perturbation h hnormX c f (j * d)
      (Nat.mul_pos (by dsimp [j]; omega) (by omega)) (j • D + d • G₀) hklt₁
      A hA (j * q) (Nat.mul_pos (by dsimp [j]; omega) (by omega)) 0 1 one_pos
      ∅ Set.finite_empty
  have hcancel : r * q = m * d := by
    apply mul_left_cancel₀ (by dsimp [j]; omega : j ≠ 0)
    calc j * (r * q) = r * (j * q) := by ring
      _ = m * (j * d) := hcommon.symm
      _ = j * (m * d) := by ring
  let τ := cartierSectionUnit (r • cartierPullback h A) s hs
  let G := m • (d • G₀) + cartierSectionZeroDivisor (r • cartierPullback h A) s hs
  have hmult : ∀ b : ℕ, (b • G₀).IsEffective := by
    intro b
    induction b with
    | zero => simpa only [zero_smul] using (CartierDivisor.isEffective_zero (X := X))
    | succ b hb => simpa only [succ_nsmul] using hb.add hG₀
  have hG : G.IsEffective := by
    apply CartierDivisor.IsEffective.add _ (cartierSectionZeroDivisor_isEffective _ s hs)
    simpa only [smul_smul] using hmult (m * d)
  refine ⟨m * j, Nat.mul_pos (by omega) (by dsimp [j]; omega), G,
    σ ^ (m * d * q) * τ ^ q, hG, ?_, ?_⟩
  · simpa only [G, nsmul_add, smul_smul, Nat.mul_assoc, add_assoc] using hklt₂
  · have hidZ : q • GZ + A = j • M + q • principalCartierDivisor Z σZ :=
      nefBig_perturbation_remainder_identity M H (principalCartierDivisor Z σZ) a q e
    have hid : q • G₀ + cartierPullback h A = j • cartierPullback h M +
        q • principalCartierDivisor X σ := by
      simpa only [cartierPullback_add, cartierPullback_nsmul, cartierPullback_principal] using
        congrArg (cartierPullback h) hidZ
    dsimp only [G]
    rw [nsmul_add, cartierSectionZeroDivisor, nsmul_add]
    have hsec : q • (r • cartierPullback h A) = (m * d) • cartierPullback h A := by
      simp only [smul_smul, Nat.mul_comm q r, hcancel]
    rw [hsec]
    simp only [principalCartierDivisor_mul, principalCartierDivisor_power]
    rw [← add_assoc]
    calc q • (m • (d • G₀)) + (m * d) • cartierPullback h A + q • principalCartierDivisor X τ =
        (m * d) • (q • G₀ + cartierPullback h A) + q • principalCartierDivisor X τ := by module
      _ = (m * d) • (j • cartierPullback h M + q • principalCartierDivisor X σ) +
          q • principalCartierDivisor X τ := by rw [hid]
      _ = _ := by module

end MixedFujita
