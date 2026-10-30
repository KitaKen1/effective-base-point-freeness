/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.NefNumericalZeroEulerNonvanishing

/-!
Geometric higher vanishing for stage 16.

The ample SNC characteristic-zero theorem supplies every positive cohomological
degree, including after signed-boundary roundup and after adding nef twists.
It therefore supplies the vanishing input in the Euler nonvanishing argument.
On a smooth SNC log Fano pair, it also supplies the entire numerical-zero
principality argument, with no cohomology or Euler-characteristic input.

The ample hypothesis is essential to the scope of this module. Higher vanishing
for a general nef-and-big klt adjoint still requires a higher-degree descent
argument; the existing H¹ descent is not used as a substitute for it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  Classical.propDecidable

/-- Signed SNC roundup has actual vanishing in every positive degree, supplied
by the characteristic-zero ample theorem rather than assumed as an input. -/
theorem signed_snc_roundup_higher_vanishing_of_charZero
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (B E Q : CartierDivisor X) (d : ℕ) (hd : 1 ≤ d)
    (hsupport : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient B (t : X) = 0)
    (hE : ∀ t : CodimensionOnePoint X, cartierCoefficient E (t : X) =
      ⌈-((cartierCoefficient B (t : X) : ℝ) / (d : ℝ))⌉)
    (hamp : CartierIsAmpleProj K (d • (Q - smoothCanonicalDivisor cX) - B))
    (j : ℕ) (hj : 1 ≤ j) :
    Subsingleton (Scheme.Modules.Cohomology (Q + E).sheaf j) :=
  signed_snc_roundup_vanishing_of_ample_KV_inDegree K
    (kawamataViehwegVanishingSNCAmpleInDegree_of_charZero K n j hj)
    cX ξ hinj hξ hsnc B E Q d hd hsupport hE hamp

section FractionalSNC

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (F : Fin r → CartierDivisor X)
    (hF : ∀ (k : Fin r) (z : CodimensionOnePoint X),
      cartierCoefficient (F k) (z : X) = if (z : X) = ξ k then 1 else 0)
    (d : ℕ) (hd : 1 ≤ d) (a : Fin r → ℕ) (ha : ∀ k, a k < d)

include hinj hξ hsnc hF hd ha

/-- An ample SNC adjoint remains ample after every nef twist, so all positive
cohomological degrees vanish for every nonnegative twist, including zero. -/
theorem snc_ample_adjoint_nef_twists_higher_vanishing
    (Q D : CartierDivisor X) (hD : CartierIsNef K D)
    (hamp : CartierIsAmpleProj K
      (d • (Q - smoothCanonicalDivisor cX) - ∑ k, a k • F k))
    (m j : ℕ) (hj : 1 ≤ j) :
    Subsingleton (Scheme.Modules.Cohomology (Q + m • D).sheaf j) := by
  apply kawamataViehwegVanishingSNCAmpleInDegree_of_charZero K n j hj
    X cX r ξ hinj hξ hsnc F hF (Q + m • D) d hd a ha
  have he : d • ((Q + m • D) - smoothCanonicalDivisor cX) - ∑ k, a k • F k =
      (d * m) • D + (d • (Q - smoothCanonicalDivisor cX) - ∑ k, a k • F k) := by
    rw [mul_smul]
    module
  rw [he]
  exact proper_nef_add_ample_isAmpleProj K _ _ (cartierIsNef_nsmul hD _) hamp

/-- An initial nonzero Euler value and an ample SNC adjoint give actual
sections in every sufficiently large nef twist. All higher vanishing is now
supplied geometrically; only the initial Euler value is explicit. -/
theorem snc_ample_adjoint_eventually_exists_nonzero_section
    (Q D : CartierDivisor X) (hD : CartierIsNef K D)
    (hamp : CartierIsAmpleProj K
      (d • (Q - smoothCanonicalDivisor cX) - ∑ k, a k • F k))
    (hχ : Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) Q.sheaf ≠ 0) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ s : Γ((Q + m • D).sheaf, ⊤), s ≠ 0 := by
  have hdim : topologicalKrullDim X ≤ n := (etaleChart_topologicalKrullDim cX).le
  have hP : cartierEulerPolynomial K n D Q ≠ 0 := by
    intro hzero
    have he := proper_cartierEulerPolynomial_eval_int K n hdim D Q 0
    rw [hzero] at he
    simp only [Polynomial.eval_zero, zero_smul, add_zero] at he
    exact hχ (by exact_mod_cast he.symm)
  obtain ⟨N, hN⟩ := rationalPolynomial_eventually_eval_nat_ne_zero _ hP
  refine ⟨N, fun m hm => moduleSections_exists_nonzero_of_eulerChar_ne_zero K _ ?_ ?_⟩
  · intro he
    apply hN m hm
    have h := proper_cartierEulerPolynomial_eval_int K n hdim D Q (m : ℤ)
    simpa only [Int.cast_natCast, natCast_zsmul, he, Int.cast_zero] using h
  · intro q
    exact snc_ample_adjoint_nef_twists_higher_vanishing K cX ξ hinj hξ hsnc F hF
      d hd a ha Q D hD hamp m (q + 1) (by omega)

/-- On a smooth SNC log Fano pair, every nef numerical-zero Cartier divisor is
principal and every nonnegative multiple is globally generated. The geometric
ample anti-log-canonical hypothesis supplies all vanishing, including at m=0;
neither an Euler invariant nor a nonzero section is an additional input. -/
theorem smooth_snc_logFano_nef_numerical_zero_principal
    (hn : 1 ≤ n) (D J : CartierDivisor X)
    (hD : CartierIsNef K D) (hJ : CartierIsAmpleProj K J)
    (hzero : cartierNumericalDimension K n (etaleChart_topologicalKrullDim cX) D J = 0)
    (hFano : CartierIsAmpleProj K
      (d • (-smoothCanonicalDivisor cX) - ∑ k, a k • F k)) :
    (∃ f : X.functionFieldˣ, D = principalCartierDivisor X f) ∧
      ∀ m : ℕ, CartierIsGloballyGenerated (m • D) := by
  apply proper_nef_numerical_zero_principal_of_all_multiples_vanishing
    K n (etaleChart_topologicalKrullDim cX) hn D J hD hJ hzero
  intro m q _
  have hamp : CartierIsAmpleProj K
      (d • ((0 : CartierDivisor X) - smoothCanonicalDivisor cX) - ∑ k, a k • F k) := by
    simpa only [zero_sub] using hFano
  simpa only [zero_add] using snc_ample_adjoint_nef_twists_higher_vanishing
    K cX ξ hinj hξ hsnc F hF d hd a ha 0 D hD hamp m (q + 1) (by omega)

end FractionalSNC

end MixedFujita
