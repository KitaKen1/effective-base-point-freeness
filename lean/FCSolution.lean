/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import FCTargetDefinitions
public import MixedFujita.LinearEffectiveFreenessNumerical

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme MixedFujita

namespace EffectiveFreenessPublication

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  let : Uncountable ℂ := Complex.ofReal_injective.uncountable
  constructor
  · intro m hm
    exact linearEffectiveFreeness_numerical ℂ hdim hnorm
      (normal_codimOneChartCovered hdim hnorm) J hJ c₀ f₀ r hr D'
      heff hklt D hD a ha hnef hbig m hm
  · exact klt_nef_numericalZero_principal ℂ hdim hnorm
      (normal_codimOneChartCovered hdim hnorm) J hJ c₀ f₀ r hr D'
      heff hklt D hD a hnef hbig

end variants

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
  obtain ⟨h, _⟩ := variants.numerical X n hdim hnorm J hJ c₀ f₀ r hr D'
    heff hklt D hD a ha hnef hbig
  exact h (a + n + 1) (by
    have hν := cartierNumericalDimension_le_dim ℂ n hdim D J
    omega)

end EffectiveFreenessPublication
