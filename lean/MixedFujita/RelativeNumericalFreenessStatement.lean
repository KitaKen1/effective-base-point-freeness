/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KawamataNumericalFreenessStatement

/-!
The statement of relative K-NF (step 17R, replacing Ambro's canonical bundle formula in F2).

K-NF asks for a klt pair on the variety that carries the sections. Relative K-NF separates the
two roles: the klt pair (X, Δ), with D = r(K_X + Δ), lives on X and supplies the vanishing
theorem, while the sections, the numerical hypotheses and the conclusion live on the base Y of a
contraction f : X → Y (f_* O_X = O_Y). For a Cartier divisor P on Y and an ample Cartier divisor
L on Y, the positivity is asked on X:

* the remainder r f*P − D − f*L is ample (so that r f*P − D is ample plus the pullback of L, and
  every combination a f*L + b (r f*P − D − f*L) with b ≥ 1 is ample);

and the numerical hypotheses are those of K-NF for L on Y, with k = dim Y in place of n:
L^k > (r(k + 1))^k and L^d · W ≥ (r(k + 1))^d for every proper positive-dimensional subvariety
W of Y, in the form of the restricted sections. The conclusion is that P is globally generated.

In F2 the contraction is that of D given by the base point free theorem and the remainder is the
ample part kept by the perturbation of §9.3; there relative K-NF replaces Ambro's formula. The
proof of K-NF in sections 1 to 7 of the manuscript goes through with the valuations, models, log
discrepancies and the Kawamata–Viehweg theorem taken on X, the sections and their growth taken
on Y, and the centres measured by their images in Y (see 工程17_Ambro迂回検討_2026-10-20.md).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Relative K-NF: let (X, Δ) be a projective klt pair with effective boundary over an
uncountable algebraically closed field of characteristic zero, D = r(K_X + Δ), and f : X → Y a
contraction (f_* O_X = O_Y) onto a normal projective variety of dimension k ≥ 1. Let P be a
Cartier divisor and L an ample Cartier divisor on Y such that r f*P − D − f*L is ample on X. If L^k > (r(k + 1))^k and L^d · W ≥ (r(k + 1))^d for every proper
positive-dimensional subvariety W of Y (in the form of the restricted sections), then P is
globally generated. -/
def RelativeNumericalFreeness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D → LogPairIsKlt c₀ f₀ r D →
    ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
      [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (k : ℕ),
      topologicalKrullDim Y = k → 1 ≤ k →
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered k K Y →
      ∀ (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))],
        (∀ V : Y.Opens, Function.Bijective (f.app V).hom) →
      ∀ P L : CartierDivisor Y, CartierIsAmpleProj K L →
        CartierIsAmpleProj K (r • cartierPullback f P - D - cartierPullback f L) →
        (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
          ((((r * (k + 1) : ℕ) : ℝ) ^ k + δ) * (j : ℝ) ^ k / k.factorial ≤
            cartierRestrictedDim K (j • L) (genericPoint Y))) →
        (∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d → d < k →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
            ((((r * (k + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
              cartierRestrictedDim K (j • L) η)) →
        CartierIsGloballyGenerated P

end MixedFujita
