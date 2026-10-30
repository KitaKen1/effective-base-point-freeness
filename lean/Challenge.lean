/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import FCTargetDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme MixedFujita

namespace EffectiveFreenessPublication

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Kollár [Kol93, p.596], for complex projective pairs and integral $a\ge1$. -/
theorem kollar (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of ℂ))] [IsProper (X ↘ Spec (CommRingCat.of ℂ))]
    (n : ℕ) (hdim : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj ℂ J)
    (c₀ : EtaleChart ℂ X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef ℂ D)
    (a : ℕ) (ha : 1 ≤ a) (hnef : CartierIsNef ℂ ((r * a) • D - D'))
    (hbig : CartierIsBig ℂ ((r * a) • D - D')) :
    CartierIsGloballyGenerated ((a + n + 1) • D) := by
  sorry

namespace variants

/-- The numerical variant: $m\ge a+\nu(D)+1$, with $D\sim0$ when $\nu(D)=0$. -/
theorem numerical (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of ℂ))] [IsProper (X ↘ Spec (CommRingCat.of ℂ))]
    (n : ℕ) (hdim : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj ℂ J)
    (c₀ : EtaleChart ℂ X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef ℂ D)
    (a : ℕ) (ha : 1 ≤ a) (hnef : CartierIsNef ℂ ((r * a) • D - D'))
    (hbig : CartierIsBig ℂ ((r * a) • D - D')) :
    (∀ m : ℕ, a + cartierNumericalDimension ℂ n hdim D J + 1 ≤ m →
      CartierIsGloballyGenerated (m • D)) ∧
    (cartierNumericalDimension ℂ n hdim D J = 0 →
      ∃ f : X.functionFieldˣ, D = principalCartierDivisor X f) := by
  sorry

end variants

end EffectiveFreenessPublication
