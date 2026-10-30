/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierBigDefinition
public import MixedFujita.ProperCurveOrderBounds

/-!
The original section-growth definition of CartierIsBig implies strictly
positive intrinsic degree on an actual proper smooth curve over an
algebraically closed field. If the degree were nonpositive, the existing
geometric order/Taylor bound would bound every graded section space by one;
the arbitrarily large linear lower bound in bigness contradicts this.
No nefness, characteristic zero or projective embedding is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- On an actual proper smooth curve, bigness forces strictly positive intrinsic degree. -/
theorem properSmoothCurve_degree_pos_of_isBig
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Smooth (X ↘ Spec (CommRingCat.of K))]
    (hX : topologicalKrullDim X = 1) (D : CartierDivisor X)
    (hD : CartierIsBig K D) : 0 < properCurveCartierDegree (K := K) hX D := by
  obtain ⟨d, hd, c, hc, hfreq⟩ := hD
  have hd1 : d = 1 := by exact_mod_cast hd.symm.trans hX
  subst d
  by_contra hpos
  have hdeg : properCurveOrderBound (K := K) hX D = 0 := by
    exact Int.toNat_eq_zero.mpr (le_of_not_gt hpos)
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton
    ⟨genericPoint X, Set.mem_univ _⟩
  have hbound (m : ℕ) : Module.finrank K Γ((m • D).sheaf, ⊤) ≤ 1 := by
    simpa only [hdeg, mul_zero, zero_add] using
      properSmoothCurve_gradedSection_finrank_le_linearBound (K := K) hX D m x hx
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / c)
  obtain ⟨m, hm, hbig⟩ := (frequently_atTop.mp hfreq) N
  have hN' : (1 : ℝ) < c * (N : ℝ) := by
    have := (div_lt_iff₀ hc).mp hN
    nlinarith
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hbound' : (Module.finrank K Γ((m • D).sheaf, ⊤) : ℝ) ≤ 1 := by
    exact_mod_cast hbound m
  simp only [pow_one] at hbig
  nlinarith

end MixedFujita
