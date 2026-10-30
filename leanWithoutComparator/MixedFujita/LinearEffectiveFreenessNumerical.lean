/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.KltBasePointFree
public import MixedFujita.SemiampleNumericalIitakaDictionary
public import MixedFujita.ZeroDimensionalCartierFreeness

/-! F2 with the numerical dimension and no Iitaka hypothesis. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The klt adjoint hypotheses imply κ(D) = ν(D). -/
theorem klt_nef_cartierIitakaDimension_numericalDimension
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X) (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D)
    (a : ℕ) (ha : 1 ≤ a) (hnef : CartierIsNef K ((r * a) • D - D'))
    (hbig : CartierIsBig K ((r * a) • D - D')) :
    CartierIitakaDimension K D (cartierNumericalDimension K n hdim D J) := by
  obtain ⟨q₀, hq₀⟩ := kltBasePointFreeStatement_holds K X n hdim hn hnorm hcov ⟨J, hJ⟩
    c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig
  exact proper_semiample_cartierIitakaDimension_numericalDimension K n hdim hn hnorm D J hJ
    ⟨q₀ + 1, by omega, hq₀ (q₀ + 1) (by omega)⟩

/-- Under the klt adjoint hypotheses, ν(D) = 0 implies D ∼ 0. -/
theorem klt_nef_numericalZero_principal
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X) (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D)
    (a : ℕ) (hnef : CartierIsNef K ((r * a) • D - D'))
    (hbig : CartierIsBig K ((r * a) • D - D'))
    (hzero : cartierNumericalDimension K n hdim D J = 0) :
    ∃ f : X.functionFieldˣ, D = principalCartierDivisor X f := by
  by_cases hn : n = 0
  · refine ⟨1, ?_⟩
    rw [zeroDimensional_cartierDivisor_eq_zero
      (by simpa only [hn, Nat.cast_zero] using hdim) D, principalCartierDivisor_one]
  have hn' : 1 ≤ n := by omega
  obtain ⟨N, hN⟩ := klt_nef_eventually_nonzero_section K hdim hn' hnorm hcov ⟨J, hJ⟩
    c₀ f₀ r hr D' heff hklt D hD a hnef hbig
  obtain ⟨s, hs⟩ := hN (N + 1) (by omega)
  exact klt_nef_numericalDimension_zero_principal_of_multiple K hdim hn' hnorm hcov J hJ
    c₀ f₀ r hr D' heff hklt D hD a hnef hbig hzero (N + 1) (by omega) s hs

/-- F2: mD is globally generated for m ≥ a + ν(D) + 1. -/
theorem linearEffectiveFreeness_numerical
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X) (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D)
    (a : ℕ) (ha : 1 ≤ a) (hnef : CartierIsNef K ((r * a) • D - D'))
    (hbig : CartierIsBig K ((r * a) • D - D'))
    (m : ℕ) (hm : a + cartierNumericalDimension K n hdim D J + 1 ≤ m) :
    CartierIsGloballyGenerated (m • D) := by
  by_cases hn : n = 0
  · exact zeroDimensional_all_cartier_multiples_globallyGenerated
      (by simpa only [hn, Nat.cast_zero] using hdim) D m
  have hn' : 1 ≤ n := by omega
  have hk := klt_nef_cartierIitakaDimension_numericalDimension K hdim hn' hnorm hcov J hJ
    c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig
  exact linearEffectiveFreeness_proved K X n hdim hn' hnorm hcov ⟨J, hJ⟩
    c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig
    (cartierNumericalDimension K n hdim D J) hk m hm

end MixedFujita
