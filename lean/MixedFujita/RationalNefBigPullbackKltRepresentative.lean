/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NefBigPullbackKltRepresentative

/-!
Clear an actual rational linear pullback presentation of the moduli Cartier
class. Scaling the constructed pair clears the extra index; the principal
witness is adjusted by multiplication and inversion, without taking roots in
the function field. Positivity is imposed on the other variety, not on the
moduli Cartier divisor itself on the original model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Every nonnegative integer multiple of an actual effective Cartier divisor
is effective. -/
theorem cartierIsEffective_nsmul {X : Scheme.{u}} [IsIntegral X]
    (G : CartierDivisor X) (hG : G.IsEffective) (p : ℕ) : (p • G).IsEffective := by
  induction p with
  | zero => simpa only [zero_smul] using (CartierDivisor.isEffective_zero (X := X))
  | succ p hp => simpa only [succ_nsmul] using hp.add hG

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n k : ℕ}
  {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of K))]

/-- An actual rational linear nef-big pullback presentation constructs the
effective klt representative of the original moduli Cartier class M/q. -/
theorem logPairIsKlt_exists_effective_of_rational_nefBig_pullback
    (h : X ⟶ Z) [IsDominant h] (hna : NefAddAmpleStatement.{u})
    (hdimZ : topologicalKrullDim Z = k) (hk : 1 ≤ k)
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z))
    (cZ : EtaleChart K Z k) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
    (M : CartierDivisor X) (A H : CartierDivisor Z)
    (hAnef : CartierIsNef K A) (hAbig : CartierIsBig K A) (hH : CartierIsAmpleProj K H)
    (p : ℕ) (hp : 1 ≤ p) (η : X.functionFieldˣ)
    (hM : p • M = cartierPullback h A + principalCartierDivisor X η)
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ (t : ℕ) (_ : 1 ≤ t) (G : CartierDivisor X) (χ : X.functionFieldˣ),
      G.IsEffective ∧ LogPairIsKlt c f (t * d) (t • D + G) ∧
      q • G = (t * d) • M + principalCartierDivisor X χ := by
  obtain ⟨t, ht, G, χ, hG, hklt', hclass⟩ :=
    logPairIsKlt_exists_effective_nefBig_pullback_representative h hna hdimZ hk hnormX hnormZ
      cZ c f d hd D hklt A H hAnef hAbig hH (p * q) (Nat.mul_pos hp hq)
  refine ⟨p * t, Nat.mul_pos hp ht, p • G, χ * (η ^ (t * d))⁻¹,
    cartierIsEffective_nsmul G hG p, ?_, ?_⟩
  · have hscaled := (logPairIsKlt_scale_denominator_iff c f (t * d) p hp (t • D + G)).mpr hklt'
    simpa only [nsmul_add, smul_smul, Nat.mul_assoc] using hscaled
  · have hpull : cartierPullback h A = p • M - principalCartierDivisor X η := by
      rw [hM]
      abel
    calc
      q • (p • G) = (p * q) • G := by module
      _ = (t * d) • cartierPullback h A + principalCartierDivisor X χ := hclass
      _ = _ := by
        rw [hpull, principalCartierDivisor_mul, principalCartierDivisor_inv,
          principalCartierDivisor_power]
        module

end MixedFujita
