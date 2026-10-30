/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltBasePointFreeIitaka
public import MixedFujita.KltResolutionHigherVanishing
public import MixedFujita.EulerPolynomialNonvanishing
public import MixedFujita.CartierEulerPolynomial
public import MixedFujita.NefNumericalZeroSectionRigidity
public import MixedFujita.NefNumericalZeroTriviality
public import MixedFujita.LinearEffectiveFreenessCurve
public import MixedFujita.CartierPowerBaseLocus
public import MixedFujita.ProjectiveAllDimensionSectionBounds
public import MixedFujita.PrincipalCartierGlobalGeneration
public import MixedFujita.KltIsolationGeneration

/-!
The easy cases of the base point free theorem with an Iitaka dimension (step 16).

Let (X, Δ) be a normal projective klt pair, D nef with a D − (K_X + Δ) nef and big, and suppose a
positive multiple m₀ D has a nonzero section (this holds when κ(D) exists).

* Nonvanishing in all large degrees (`klt_nef_eventually_exists_nonzero_section_of_multiple`). On
  the klt resolution model p : T → X with exceptional round-up E, h⁰(X, m D) = h⁰(T, p*(m D) + E)
  equals the Euler characteristic for m ≥ a, a polynomial P(m). Since P(m₀ j) ≥ 1, the
  polynomial is nonzero, so P(m) ≠ 0 for all large m. No non-vanishing theorem is needed.
* Numerical dimension zero (`klt_nef_numericalDimension_zero_principal_of_multiple`). Then every
  nonzero section of a multiple makes that multiple principal; two consecutive large multiples
  are principal, so D itself is principal.
* Curves, from `linearEffectiveFreeness_normalCurve`.

What remains is the removal of points of a stable base locus when ν(D) ≥ 1 and dim X ≥ 2,
`KltStableBaseLocusRemovalStatement`; `kltBasePointFreeIitakaStatement_of_removal` reduces the base
point free theorem with an Iitaka dimension to it.
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

/-- The inverse of an isomorphism of modules does not kill nonzero global sections. -/
theorem modulesIso_inv_app_top_ne_zero {X : Scheme.{u}} {M N : X.Modules} (b : M ≅ N)
    (t : Γ(N, ⊤)) (ht : t ≠ 0) : Scheme.Modules.Hom.app b.inv ⊤ t ≠ 0 := by
  intro h
  apply ht
  have h1 : Scheme.Modules.Hom.app b.hom ⊤ (Scheme.Modules.Hom.app b.inv ⊤ t) = t :=
    ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤) b.inv_hom_id) t
  rw [h, map_zero] at h1
  exact h1.symm

/-- The isomorphism of modules does not kill nonzero global sections either. -/
theorem modulesIso_hom_app_top_ne_zero {X : Scheme.{u}} {M N : X.Modules} (b : M ≅ N)
    (t : Γ(M, ⊤)) (ht : t ≠ 0) : Scheme.Modules.Hom.app b.hom ⊤ t ≠ 0 :=
  modulesIso_inv_app_top_ne_zero b.symm t ht

/-- **Nonvanishing in all large degrees from one nonzero multiple.** For a normal projective klt
pair and a nef D with (r a) D − D' nef and big (D' = r (K_X + Δ)), if some positive multiple of D
has a nonzero section then every sufficiently large multiple does. -/
theorem klt_nef_eventually_exists_nonzero_section_of_multiple
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (hproj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D) (a : ℕ)
    (hnef : CartierIsNef K ((r * a) • D - D')) (hbig : CartierIsBig K ((r * a) • D - D'))
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (s₀ : Γ((m₀ • D).sheaf, ⊤)) (hs₀ : s₀ ≠ 0) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ s : Γ((m • D).sheaf, ⊤), s ≠ 0 := by
  let : IsProper (X ↘ Spec (CommRingCat.of K)) := isProper_structureMap_of_exists_ample_cartier hproj
  obtain ⟨H, hH⟩ := hproj
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, ρ, ξ, J, E,
    hinj, hξ, hsnc, hJ, hE, hexc, hEc, hpush, hvan⟩ :=
    exists_klt_resolution_higher_vanishing_model K hnorm hcov c₀ f₀ r hr D' heff hklt
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  have hdimT : topologicalKrullDim T ≤ n := (etaleChart_topologicalKrullDim cT).le
  -- vanishing upstairs for every m ≥ a
  have hvanm : ∀ m : ℕ, a ≤ m → ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (cartierPullback p (m • D) + E).sheaf (q + 1)) := by
    intro m hm q
    have hsplit : r • (m • D) - D' = ((r * a) • D - D') + (r * (m - a)) • D := by
      rw [smul_smul, show r * m = r * a + r * (m - a) by
        rw [← Nat.mul_add, Nat.add_sub_cancel' hm], add_smul]
      abel
    have hnefm : CartierIsNef K (r • (m • D) - D') := by
      rw [hsplit]
      exact cartierIsNef_add hnef (cartierIsNef_nsmul hD _)
    have hbigm : CartierIsBig K (r • (m • D) - D') := by
      rw [hsplit]
      exact cartierIsBig_add_of_isNef_on_projective hdim hn hnorm hH hbig (cartierIsNef_nsmul hD _)
    exact (hvan (m • D) hnefm hbigm).1 (q + 1) (by omega)
  -- sections downstairs are sections upstairs
  have hsec : ∀ m : ℕ, (∃ t : Γ((cartierPullback p (m • D) + E).sheaf, ⊤), t ≠ 0) ↔
      ∃ s : Γ((m • D).sheaf, ⊤), s ≠ 0 := by
    intro m
    obtain ⟨b⟩ := hpush (m • D)
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨Scheme.Modules.Hom.app b.inv ⊤ t, modulesIso_inv_app_top_ne_zero b t ht⟩
    · rintro ⟨s, hs⟩
      exact ⟨Scheme.Modules.Hom.app b.hom ⊤ s, modulesIso_hom_app_top_ne_zero b s hs⟩
  -- the Euler polynomial upstairs
  set P := cartierEulerPolynomial K n (cartierPullback p D) E with hPdef
  have hPeval : ∀ m : ℕ, P.eval (m : ℚ) = (Scheme.Modules.eulerChar
      (T ↘ Spec (CommRingCat.of K)) (cartierPullback p (m • D) + E).sheaf : ℚ) := by
    intro m
    have h := proper_cartierEulerPolynomial_eval_int K n hdimT (cartierPullback p D) E (m : ℤ)
    rw [cartierPullback_nsmul, add_comm]
    simpa only [Int.cast_natCast, natCast_zsmul] using h
  have hP : P ≠ 0 := by
    intro hz
    set j := m₀ * (a + 1) with hj
    have hja : a ≤ j := by
      rw [hj]
      nlinarith
    have hjD : (a + 1) • (m₀ • D) = j • D := by rw [smul_smul, hj, mul_comm]
    have hex : ∃ s : Γ(((a + 1) • (m₀ • D)).sheaf, ⊤), s ≠ 0 :=
      ⟨_, cartierSectionPower_ne_zero _ s₀ hs₀ _⟩
    rw [hjD] at hex
    obtain ⟨t, ht⟩ := (hsec j).mpr hex
    have hχ := moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero K
      (cartierPullback p (j • D) + E).sheaf (hvanm j hja)
    let : FiniteDimensional K Γ((cartierPullback p (j • D) + E).sheaf, ⊤) :=
      cartier_finiteDimensional_sections_of_ample (etaleChart_topologicalKrullDim cT) hn hJ _
    have hpos : 0 < Module.finrank K Γ((cartierPullback p (j • D) + E).sheaf, ⊤) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨t, ht⟩
    have hev := hPeval j
    rw [hz, Polynomial.eval_zero, hχ] at hev
    have h0 : Module.finrank K Γ((cartierPullback p (j • D) + E).sheaf, ⊤) = 0 := by
      exact_mod_cast hev.symm
    omega
  obtain ⟨N, hN⟩ := rationalPolynomial_eventually_eval_nat_ne_zero P hP
  refine ⟨max N a, fun m hm => (hsec m).mp ?_⟩
  apply moduleSections_exists_nonzero_of_eulerChar_ne_zero K _ ?_ (hvanm m (le_of_max_le_right hm))
  intro hz
  apply hN m (le_of_max_le_left hm)
  rw [hPeval m, hz, Int.cast_zero]

/-- **Numerical dimension zero.** If moreover ν(D) = 0 against an ample J, then D is principal:
every nonzero section of a multiple makes that multiple principal, and there are nonzero sections
in two consecutive large degrees. -/
theorem klt_nef_numericalDimension_zero_principal_of_multiple
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D) (a : ℕ)
    (hnef : CartierIsNef K ((r * a) • D - D')) (hbig : CartierIsBig K ((r * a) • D - D'))
    (hzero : cartierNumericalDimension K n hdim D J = 0)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (s₀ : Γ((m₀ • D).sheaf, ⊤)) (hs₀ : s₀ ≠ 0) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  obtain ⟨N, hN⟩ := klt_nef_eventually_exists_nonzero_section_of_multiple K hdim hn hnorm hcov
    ⟨J, hJ⟩ c₀ f₀ r hr D' heff hklt D hD a hnef hbig m₀ hm₀ s₀ hs₀
  obtain ⟨s, hs⟩ := hN (N + 1) (by omega)
  obtain ⟨s', hs'⟩ := hN (N + 1 + 1) (by omega)
  obtain ⟨⟨φ, hφ⟩, -⟩ := proper_nef_numerical_zero_section_seed_principal_multiple_and_numericallyTrivial
    K n hdim hn D J hD hJ hzero (N + 1) (by omega) s hs
  obtain ⟨⟨φ', hφ'⟩, -⟩ := proper_nef_numerical_zero_section_seed_principal_multiple_and_numericallyTrivial
    K n hdim hn D J hD hJ hzero (N + 1 + 1) (by omega) s' hs'
  refine ⟨φ' * φ⁻¹, ?_⟩
  have hsplit : D = (N + 1 + 1) • D - (N + 1) • D := by
    rw [add_smul _ 1 D, one_smul]
    abel
  rw [hsplit, hφ, hφ', principalCartierDivisor_mul, principalCartierDivisor_inv]
  abel

/-- The remaining case of the base point free theorem with an Iitaka dimension: a point of a
nonempty stable base locus of the powers b^e D is removed by a higher power, when dim X ≥ 2, the
numerical dimension of D is positive and D has nonzero sections in all large degrees. -/
def KltStableBaseLocusRemovalStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n), 2 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    ∀ J : CartierDivisor X, CartierIsAmpleProj K J →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D' : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D' → LogPairIsKlt c₀ f₀ r D' →
    ∀ D : CartierDivisor X, CartierIsNef K D → ∀ a : ℕ, 1 ≤ a →
      CartierIsNef K ((r * a) • D - D') → CartierIsBig K ((r * a) • D - D') →
      ∀ N : ℕ, (∀ m : ℕ, N ≤ m → ∃ s : Γ((m • D).sheaf, ⊤), s ≠ 0) →
      1 ≤ cartierNumericalDimension K n hdim D J →
      ∀ b : ℕ, 2 ≤ b → ∀ e : ℕ, N ≤ b ^ e →
        (∀ f : ℕ, e ≤ f → cartierBaseLocus ((b ^ f) • D) = cartierBaseLocus ((b ^ e) • D)) →
        (cartierBaseLocus ((b ^ e) • D) : Set X).Nonempty →
          ∃ (f : ℕ) (x : X), e ≤ f ∧ x ∈ cartierBaseLocus ((b ^ e) • D) ∧
            x ∉ cartierBaseLocus ((b ^ f) • D)

/-- The base point free theorem with an Iitaka dimension from the removal of points of stable base
loci. The curve case, the numerical-dimension-zero case and nonvanishing are proved here. -/
theorem kltBasePointFreeIitakaStatement_of_removal
    (hrem : KltStableBaseLocusRemovalStatement.{u}) : KltBasePointFreeIitakaStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hproj c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig
    k hk
  let : IsProper (X ↘ Spec (CommRingCat.of K)) := isProper_structureMap_of_exists_ample_cartier hproj
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  obtain ⟨H, hH⟩ := hproj
  -- a nonzero section of a positive multiple
  obtain ⟨⟨c, hc, hfreq⟩, -⟩ := hk
  obtain ⟨m₀, hm₀c, hm₀⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
  have hpos : 0 < Module.finrank K Γ((m₀ • D).sheaf, ⊤) := by
    have h1 : (0 : ℝ) < c * (m₀ : ℝ) ^ k := by
      have : (1 : ℝ) ≤ m₀ := by exact_mod_cast hm₀
      positivity
    exact_mod_cast h1.trans_le hm₀c
  have : Nontrivial Γ((m₀ • D).sheaf, ⊤) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨s₀, hs₀⟩ := exists_ne (0 : Γ((m₀ • D).sheaf, ⊤))
  -- curves
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact ⟨a + 1, fun m hm => linearEffectiveFreeness_normalCurve hdim hnorm ⟨H, hH⟩ c₀ f₀ r hr D'
      heff D hD a hbig m hm⟩
  -- nonvanishing in all large degrees
  obtain ⟨N, hN⟩ := klt_nef_eventually_exists_nonzero_section_of_multiple K hdim hn hnorm hcov
    ⟨H, hH⟩ c₀ f₀ r hr D' heff hklt D hD a hnef hbig m₀ hm₀ s₀ hs₀
  by_cases hν : cartierNumericalDimension K n hdim D H = 0
  · obtain ⟨φ, hφ⟩ := klt_nef_numericalDimension_zero_principal_of_multiple K hdim hn hnorm hcov
      H hH c₀ f₀ r hr D' heff hklt D hD a hnef hbig hν m₀ hm₀ s₀ hs₀
    refine ⟨0, fun q _ => ?_⟩
    rw [hφ, ← principalCartierDivisor_power]
    exact principalCartierDivisor_globallyGenerated (φ ^ q)
  have hν1 : 1 ≤ cartierNumericalDimension K n hdim D H := Nat.one_le_iff_ne_zero.mpr hν
  apply cartier_eventually_generated_of_two_stable_base_locus_removals D 2 3 N (by norm_num)
    (by norm_num)
  intro b hb e he hstable hne
  have hb2 : 2 ≤ b := by
    rcases hb with rfl | rfl
    · exact le_rfl
    · norm_num
  have hpow : N ≤ b ^ e := le_trans he (Nat.lt_pow_self (by omega)).le
  exact hrem K X n hdim hn2 hnorm hcov H hH c₀ f₀ r hr D' heff hklt D hD a ha hnef hbig N hN hν1
    b hb2 e hpow hstable hne

end MixedFujita
