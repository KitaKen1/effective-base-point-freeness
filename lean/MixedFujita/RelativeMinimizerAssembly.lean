/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeKltIsolationGeneration
public import MixedFujita.RelativeWeightProfiles
public import MixedFujita.KltMinimizerDataShift
public import MixedFujita.KltMinimizerDataPowers

/-!
The data of the minimizer for relative K-NF from a minimizing profile datum over a fibre (step
17R-2, sections 3.2 and 6.1 of the manuscript relative to f).

Let (V, B) be a projective klt pair, f : V → Y and y a point of the base. A profile datum of a
tuple of sections of j f*L over the fibre of y (`relWeightProfiles`) has the fibre-centre property
(`RelWeightProfileHasFibreCentre`) when, on every proper simple normal crossing model π : X → V and
every weight over π⁻¹(f⁻¹(y)) with that datum, every point of the model whose closure meets
π⁻¹(f⁻¹(y)) and whose polytope contains the normalized profile lies in π⁻¹(f⁻¹(y)). This is the
conclusion of section 5 relative to f: the centre of a minimizing pair maps to the point y of the
base.

* `relIsolationMinimizerData_of_minimal_relWeightProfile_shift`: a datum minimal among the data of
  the tuple over the fibre, with objective smaller than N and the fibre-centre property, gives
  `RelIsolationMinimizerData` for A when l A = J + div φ on Y and d l t < 1: the weight is a
  minimizer among the weights over π⁻¹(f⁻¹(y)) on its model, so the first-order conditions give c,
  q, the inequality (24) and the budget, and the principal shift turns the sections of j f*J into
  sections of (l j) f*A with the same zero divisors;
* `relIsolationMinimizerData_of_relIsolationMinimizerData`: data for one m₁ give data for every
  m₀ ≥ 1 (powers of the sections).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Centre

variable {K : Type u} [Field K] {n : ℕ} {V Y : Scheme.{u}} [IsIntegral V]
  [IsLocallyNoetherian V] [V.Over (Spec (CommRingCat.of K))]

/-- The fibre-centre property of a profile datum p of the tuple s over the fibre of y: on every
proper simple normal crossing model and every weight over the preimage of the fibre of y with datum
p, every point whose closure meets that preimage and whose polytope contains the normalized profile
lies in it. -/
def RelWeightProfileHasFibreCentre (cV : EtaleChart K V n) (fV : V.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor V) (f : V ⟶ Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    (p : ℝ × (Fin N → ℝ)) : Prop :=
  ∀ (hs : ∀ i, s i ≠ 0) (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (π : X ⟶ V) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    (r : ℕ) (ξ : Fin r → X) (w : Fin r → ℝ), Function.Injective ξ →
    (∀ k, Order.coheight (ξ k) = 1) → IsSNCFamily K n ξ →
    (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover)
        (z : X) = 0) →
    (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (z : X) = 0) →
    (∀ k, 0 ≤ w k) →
    (∃ z ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)), ∀ k, w k ≠ 0 → z ∈ closure ({ξ k} : Set X)) →
    p.1 = ∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover) (ξ k)) / d) →
    (∀ i, p.2 i = ∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) →
    ∀ pt : X, (closure ({pt} : Set X) ∩ π ⁻¹' (f ⁻¹' ({y} : Set Y))).Nonempty →
      InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (fun i => p.2 i / p.1) pt →
      pt ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y))

end Centre

section Data

variable {K : Type u} [Field K] {n : ℕ} {V Y : Scheme.{u}} [IsIntegral V]
  [IsLocallyNoetherian V] [V.Over (Spec (CommRingCat.of K))] [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The data of the minimizer for relative K-NF from data with sections of a divisor E equal to
j f*L. -/
theorem relIsolationMinimizerData_of_eq_nsmul (cV : EtaleChart K V n) (fV : V.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor V) (f : V ⟶ Y) [IsDominant f] (L : CartierDivisor Y) (m₀ : ℕ)
    (y : Y) (E : CartierDivisor V) (j : ℕ) (hE : E = j • cartierPullback f L) (hjm₀ : m₀ ∣ j)
    {N : ℕ} (s : Fin N → Γ(E.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (π : X ⟶ V) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (z : X) (c q : Fin N → ℝ)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ w : CodimensionOnePoint X, (w : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) (w : X) =
        0)
    (hDsupp : ∀ i, ∀ w : CodimensionOnePoint X, (w : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) (w : X) =
        0)
    (hz : f (π z) = y) (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqz : InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) q z)
    (hpoly : ∀ p ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)), InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) q p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor E (s i) (hs i))) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) (ξ k)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' (f ⁻¹' ({y} : Set Y))).Nonempty →
      InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor E (s i) (hs i))) q p →
      p ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    RelIsolationMinimizerData cV fV d D f L m₀ y := by
  subst hE
  exact ⟨j, N, s, hs, X, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, π, inferInstance, inferInstance, inferInstance, hπ, cX, r, ξ, z, c, q, hjm₀,
    hinj, hξ, hsnc, hBsupp, hDsupp, hz, hc, hcq, hqz, hpoly, hcentre, hbudget⟩

/-- The data of the minimizer for relative K-NF for some m₁ give the data for every m₀ ≥ 1: the
m₀-th powers of the sections, with c/m₀ and m₀ q, are data at the degree m₀ j. -/
theorem relIsolationMinimizerData_of_relIsolationMinimizerData (cV : EtaleChart K V n)
    (fV : V.functionFieldˣ) (d : ℕ) (D : CartierDivisor V) (f : V ⟶ Y) [IsDominant f]
    (L : CartierDivisor Y) {m₁ : ℕ} (y : Y) (h : RelIsolationMinimizerData cV fV d D f L m₁ y)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    RelIsolationMinimizerData cV fV d D f L m₀ y := by
  obtain ⟨j, N, s, hs, X, hXi, hXN, hXo, hXp, hXs, π, hdom, hover, hprop, hπ, cX, r, ξ, z, c, q,
    -, hinj, hξ, hsnc, hBsupp, hDsupp, hz, hc, hcq, hqz, hpoly, hcentre, hbudget⟩ := h
  have hk : 0 < m₀ := hm₀
  have hk' : (0 : ℝ) < (m₀ : ℝ) := by exact_mod_cast hk
  -- the powers of the sections and their zero divisors
  have hs' : ∀ i, cartierSectionPower (j • cartierPullback f L) (s i) m₀ ≠ 0 := fun i =>
    cartierSectionPower_ne_zero (j • cartierPullback f L) (s i) (hs i) m₀
  have hzero : ∀ i, cartierPullback π (cartierSectionZeroDivisor (m₀ • j • cartierPullback f L)
      (cartierSectionPower (j • cartierPullback f L) (s i) m₀) (hs' i)) =
      m₀ • cartierPullback π
        (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i)) := fun i => by
    rw [cartierSectionZeroDivisor_power, cartierPullback_nsmul]
  have hcoef : ∀ i (w : X), (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
      (m₀ • j • cartierPullback f L) (cartierSectionPower (j • cartierPullback f L) (s i) m₀)
        (hs' i))) w : ℝ) =
      (m₀ : ℝ) * cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) w := fun i w => by
    rw [hzero i, cartierCoefficient_nsmul]
    push_cast
    ring
  -- the polytopes are multiplied by m₀
  have hpolyiff : ∀ p : X, InSNCProfilePolytope ξ d
      (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor (m₀ • j • cartierPullback f L)
        (cartierSectionPower (j • cartierPullback f L) (s i) m₀) (hs' i)))
        (fun i => (m₀ : ℝ) * q i) p ↔
      InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (fun i => cartierPullback π
          (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) q p :=
    fun p => by
      simp only [hzero]
      exact inSNCProfilePolytope_nsmul_iff ξ d _ _ q p hk
  refine relIsolationMinimizerData_of_eq_nsmul cV fV d D f L m₀ y
    (m₀ • j • cartierPullback f L) (m₀ * j) (smul_smul m₀ j _) (dvd_mul_right m₀ j)
    (fun i => cartierSectionPower (j • cartierPullback f L) (s i) m₀) hs'
    X π hπ cX ξ z (fun i => c i / m₀) (fun i => (m₀ : ℝ) * q i) hinj hξ hsnc hBsupp ?_ hz ?_ ?_
    ((hpolyiff z).mpr hqz) ?_ (fun p hp hpq => hcentre p hp ((hpolyiff p).mp hpq)) ?_
  · intro i w hw
    rw [hzero i, cartierCoefficient_nsmul, hDsupp i w hw, mul_zero]
  · exact fun i => div_pos (hc i) hk'
  · rw [← hcq]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · intro p hp hpq k hkp
    have h := hpoly p hp ((hpolyiff p).mp hpq) k hkp
    calc ∑ i, c i / m₀ * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (m₀ • j • cartierPullback f L) (cartierSectionPower (j • cartierPullback f L) (s i) m₀)
            (hs' i))) (ξ k) : ℝ)
        = ∑ i, c i * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) (ξ k) : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hcoef i]
          field_simp
      _ ≤ _ := h
  · have heq : ((d * (m₀ * j) : ℕ) : ℝ) * ∑ i, c i / m₀ = ((d * j : ℕ) : ℝ) * ∑ i, c i := by
      rw [← Finset.sum_div]
      push_cast
      field_simp
    rw [heq]
    exact hbudget

variable [IsProper (V ↘ Spec (CommRingCat.of K))]

/-- The data of the minimizer for relative K-NF for a divisor A of the base with l A = J + div φ,
from a profile datum over the fibre of y of a tuple of sections of j f*J which is minimal among
the data of the tuple over the fibre, has objective smaller than N and has the fibre-centre
property, when d l t < 1. -/
theorem relIsolationMinimizerData_of_minimal_relWeightProfile_shift
    (cV : EtaleChart K V n) (fV : V.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor V)
    (hklt : LogPairIsKlt cV fV d D₀) (f : V ⟶ Y) [IsDominant f] (J A : CartierDivisor Y) {l : ℕ}
    (φ : Y.functionFieldˣ) (hlA : l • A = J + principalCartierDivisor Y φ) (y : Y)
    (j : ℕ) (hj : 1 ≤ j) {N : ℕ} (hN : 0 < N)
    (s : Fin N → Γ((j • cartierPullback f J).sheaf, ⊤)) {t : ℝ} (ht : 0 < t)
    (hdt : (d : ℝ) * l * t < 1)
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ relWeightProfiles cV fV d D₀ (j • cartierPullback f J) f y s)
    (hmin : ∀ p' ∈ relWeightProfiles cV fV d D₀ (j • cartierPullback f J) f y s,
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j))
    (hlt : (∑ i, Real.exp (p.1 / t - p.2 i / j)) < N)
    (hpc : RelWeightProfileHasFibreCentre cV fV d D₀ (j • cartierPullback f J) f y s p) :
    RelIsolationMinimizerData cV fV d D₀ f A 1 y := by
  obtain ⟨x, hxy, hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
    hBsupp, hGsupp, hw0, ⟨z, hz, hwz⟩, hA, hv⟩ := hp
  have hXprop : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hzf : z ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)) := by
    change f (π z) = y
    rw [show π z = x from hz]
    exact hxy
  have hb : ∀ k, cartierCoefficient (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover)
      (ξ k) < (d : ℤ) := fun k =>
    logPairIsKlt_crepantBoundary_coefficient_lt π hπ cV fV d D₀ hklt cX ⟨ξ k, hξ k⟩
  -- the objective of the weight is the objective of its datum
  have hL : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • cartierPullback f J) (s i) (hs i))) (ξ k) : ℝ)) t j w =
      ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
    unfold weightExponentialObjective
    rw [hA]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]
  -- the weight is a minimizer among the weights over the preimage of the fibre
  have hwmin : ∀ w' : Fin r → ℝ, (∀ k, 0 ≤ w' k) →
      (∃ p' ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)), ∀ k, w' k ≠ 0 → p' ∈ closure ({ξ k} : Set X)) →
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • cartierPullback f J) (s i) (hs i))) (ξ k) : ℝ)) t j w ≤
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • cartierPullback f J) (s i) (hs i))) (ξ k) : ℝ)) t j
        w' := by
    rintro w' hw'0 ⟨p', hp', hp'w⟩
    have h := hmin (∑ k, w' k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover) (ξ k)) / d),
      fun i => ∑ k, w' k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • cartierPullback f J) (s i) (hs i))) (ξ k) : ℝ))
      ⟨π p', hp', hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w', hinj, hξ, hsnc,
        hBsupp, hGsupp, hw'0, ⟨p', rfl, hp'w⟩, rfl, fun i => rfl⟩
    rw [hL]
    exact h
  -- the weight is not zero
  have hwne : ∃ k, w k ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : p.1 = 0 := by
      rw [hA]
      simp [hall]
    have hv0 : ∀ i, p.2 i = 0 := fun i => by
      rw [hv i]
      simp [hall]
    simp only [h0, hv0, zero_div, sub_zero, Real.exp_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨hc, hcq, hqz, hpoly, hsum⟩ := isolation_data_of_sncWeight_minimizer hN ξ d hd _ hb
    (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f J) (s i) (hs i)))
    (π ⁻¹' (f ⁻¹' ({y} : Set Y))) ht j hj w hw0 z hzf hwz hwne hwmin
  have hcentre := hpc hs X π hπ cX r ξ w hinj hξ hsnc hBsupp hGsupp hw0 ⟨z, hzf, hwz⟩ hA hv
  have hq : (fun i => p.2 i / p.1) = fun i => (∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor (j • cartierPullback f J) (s i) (hs i))) (ξ k) : ℝ)) /
      ∑ k, w k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cV fV d D₀ cX etaleCharts_cover) (ξ k)) / d) := by
    funext i
    rw [hv i, hA]
  rw [hq] at hcentre
  -- the sections of (l j) f*A: the principal shifts of the sections of j f*J
  set φV : V.functionFieldˣ := Units.map (dominantFunctionFieldMap f).hom.toMonoidHom φ with hφV
  have hlAV : l • cartierPullback f A = cartierPullback f J + principalCartierDivisor V φV := by
    rw [← cartierPullback_nsmul, hlA, cartierPullback_add, cartierPullback_principal]
  have hE : (l * j) • cartierPullback f A =
      j • cartierPullback f J + principalCartierDivisor V (φV ^ j) := by
    rw [mul_comm, ← smul_smul, hlAV, smul_add, principalCartierDivisor_power]
  set s' : Fin N → Γ((j • cartierPullback f J + principalCartierDivisor V (φV ^ j)).sheaf, ⊤) :=
    fun i => (cartierPrincipalShiftEquiv (K := K) (j • cartierPullback f J) (φV ^ j)).symm (s i)
    with hs'def
  have hs' : ∀ i, s' i ≠ 0 := fun i => (LinearEquiv.map_ne_zero_iff _).mpr (hs i)
  have hZ : ∀ i, cartierSectionZeroDivisor
      (j • cartierPullback f J + principalCartierDivisor V (φV ^ j)) (s' i) (hs' i) =
      cartierSectionZeroDivisor (j • cartierPullback f J) (s i) (hs i) := by
    intro i
    rw [← cartierSectionZeroDivisor_principalShift (K := K) (j • cartierPullback f J) (φV ^ j)
      (s' i) (hs' i)]
    exact cartierSectionZeroDivisor_eq_of_eq
      ((cartierPrincipalShiftEquiv (K := K) (j • cartierPullback f J) (φV ^ j)).apply_symm_apply
        (s i)) _ _
  refine relIsolationMinimizerData_of_eq_nsmul cV fV d D₀ f A 1 y _ (l * j) hE.symm (one_dvd _)
    s' hs' X π hπ cX ξ z _ _ hinj hξ hsnc hBsupp ?_ ?_ hc hcq ?_ ?_ ?_ ?_
  · intro i w' hw'
    rw [hZ i]
    exact hGsupp i w' hw'
  · exact hzf
  · simp only [hZ]
    exact hqz
  · simp only [hZ]
    exact hpoly
  · simp only [hZ]
    exact hcentre
  · have hcast : ((d * (l * j) : ℕ) : ℝ) = (d : ℝ) * l * (j : ℝ) := by push_cast; ring
    rw [hcast, mul_assoc, hsum]
    exact hdt

end Data

end MixedFujita
