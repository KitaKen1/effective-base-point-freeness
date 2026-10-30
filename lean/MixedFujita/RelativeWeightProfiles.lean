/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosedPointProfiles
public import MixedFujita.SNCWeightProfileExistence
public import MixedFujita.RealizationSpecialization

/-!
Profile data over a fibre (step 17R-2, sections 2.3 and 3 of the manuscript for relative K-NF).

For relative K-NF the klt pair lives on X and the sections are pulled back from the base of a
morphism f : X → Y. The objects of sections 2 and 3 at a point y of the base are those of the pair
over the whole fibre f⁻¹(y):

* `relWeightProfiles`: the profile data of a tuple of sections at the points of the fibre, the
  union over x with f x = y of `sncWeightProfiles` at x;
* `relWeightObjectiveValues`, `relWeightInfimum`: the values of the objective at these data and
  their infimum (the quantity N f_{j,t}(y) of section 2.3 relative to f);
* `relWeightNormalizedProfiles`: the normalized profiles realized over the fibre.

The infimum over the fibre is at most the infimum at every point of the fibre. Profile data only
grow under specialization (`sncWeightProfiles_of_specializes`, from the properness of the models),
so on a proper Jacobson X the realization loci over the base are closed on closed points when the
loci of the pair on X are (`relWeightNormalizedProfiles_isClosedOnClosedPoints`): the closed
representative is the image under the closed map f. This gives the specialization comparison (6)
over the base at very general points (`relWeight_specialization_comparison_of_closedPoints`) with
the same proof as for a point.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Definitions

variable {K : Type u} [Field K] {n : ℕ} {X Y : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- The profile data of a tuple of sections over the fibre of y: the profile data of the pair on X
at the points x of X with f x = y. -/
def relWeightProfiles (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) :
    Set (ℝ × (Fin N → ℝ)) :=
  {p | ∃ x : X, f x = y ∧ p ∈ sncWeightProfiles cX fX d D₀ D x s}

/-- The values of the objective at the profile data over the fibre of y of all bases of N
elements of the sections of D. -/
def relWeightObjectiveValues (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) (N : ℕ) (t j : ℝ) : Set ℝ :=
  {val | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤), ∃ p ∈ relWeightProfiles cX fX d D₀ D f y B,
    val = ∑ i, Real.exp (p.1 / t - p.2 i / j)}

/-- The infimum of the objective over all bases and all weights over the fibre of y. -/
noncomputable def relWeightInfimum (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) (N : ℕ) (t j : ℝ) : ℝ :=
  sInf (relWeightObjectiveValues cX fX d D₀ D f y N t j)

/-- The normalized profiles realized over the fibre of y by the bases of N sections of D. -/
def relWeightNormalizedProfiles (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (N : ℕ) (y : Y) : Set (Fin N → ℝ) :=
  {q | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤), ∃ p ∈ relWeightProfiles cX fX d D₀ D f y B,
    0 < p.1 ∧ ∀ i, q i * p.1 ≤ p.2 i}

theorem relWeightObjectiveValues_nonneg (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) (N : ℕ) (t j : ℝ) :
    ∀ val ∈ relWeightObjectiveValues cX fX d D₀ D f y N t j, 0 ≤ val := by
  rintro val ⟨B, p, -, rfl⟩
  exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

theorem relWeightInfimum_nonneg (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) (N : ℕ) (t j : ℝ) :
    0 ≤ relWeightInfimum cX fX d D₀ D f y N t j :=
  Real.sInf_nonneg (relWeightObjectiveValues_nonneg cX fX d D₀ D f y N t j)

/-- The infimum over the fibre is at most the objective of every profile datum over the fibre. -/
theorem relWeightInfimum_le (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) {N : ℕ} (t j : ℝ)
    (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) {p : ℝ × (Fin N → ℝ)}
    (hp : p ∈ relWeightProfiles cX fX d D₀ D f y B) :
    relWeightInfimum cX fX d D₀ D f y N t j ≤ ∑ i, Real.exp (p.1 / t - p.2 i / j) :=
  csInf_le ⟨0, relWeightObjectiveValues_nonneg cX fX d D₀ D f y N t j⟩ ⟨B, p, hp, rfl⟩

/-- A common lower bound of the objective over the fibre bounds the infimum. -/
theorem le_relWeightInfimum (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) (N : ℕ) (t j : ℝ)
    (hne : (relWeightObjectiveValues cX fX d D₀ D f y N t j).Nonempty) {L : ℝ}
    (hL : ∀ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      ∀ p ∈ relWeightProfiles cX fX d D₀ D f y B, L ≤ ∑ i, Real.exp (p.1 / t - p.2 i / j)) :
    L ≤ relWeightInfimum cX fX d D₀ D f y N t j := by
  refine le_csInf hne ?_
  rintro val ⟨B, p, hp, rfl⟩
  exact hL B p hp

/-- The infimum over the fibre is at most the infimum at every point of the fibre. -/
theorem relWeightInfimum_le_sncWeightInfimum (cX : EtaleChart K X n) (fX : X.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor X) (f : X ⟶ Y) {x : X} {y : Y} (hx : f x = y) (N : ℕ)
    (t j : ℝ) (hne : (sncWeightObjectiveValues cX fX d D₀ D x N t j).Nonempty) :
    relWeightInfimum cX fX d D₀ D f y N t j ≤ sncWeightInfimum cX fX d D₀ D x N t j := by
  apply le_csInf hne
  rintro val ⟨B, p, hp, rfl⟩
  exact relWeightInfimum_le cX fX d D₀ D f y t j B ⟨x, hx, hp⟩

theorem mem_relWeightNormalizedProfiles_iff (cX : EtaleChart K X n) (fX : X.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor X) (f : X ⟶ Y) (N : ℕ) (y : Y) (q : Fin N → ℝ) :
    q ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y ↔
      ∃ x : X, f x = y ∧ q ∈ sncWeightNormalizedProfiles cX fX d D₀ D N x := by
  constructor
  · rintro ⟨B, p, ⟨x, hx, hp⟩, hp1, hq⟩
    exact ⟨x, hx, B, p, hp, hp1, hq⟩
  · rintro ⟨x, hx, B, p, hp, hp1, hq⟩
    exact ⟨B, p, ⟨x, hx, hp⟩, hp1, hq⟩

/-- The normalized profiles over the fibre are downward closed. -/
theorem relWeightNormalizedProfiles_down (cX : EtaleChart K X n) (fX : X.functionFieldˣ)
    (d : ℕ) (D₀ D : CartierDivisor X) (f : X ⟶ Y) (N : ℕ) (y : Y) :
    ∀ q ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y, ∀ q', q' ≤ q →
      q' ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y := by
  rintro q ⟨B, p, hp, hp1, hq⟩ q' hq'
  exact ⟨B, p, hp, hp1, fun i => (mul_le_mul_of_nonneg_right (hq' i) hp1.le).trans (hq i)⟩

/-- Scaling the weight scales the profile datum over the fibre. -/
theorem relWeightProfiles_scale (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ relWeightProfiles cX fX d D₀ D f y s) {c : ℝ} (hc : 0 < c) :
    (c * p.1, fun i => c * p.2 i) ∈ relWeightProfiles cX fX d D₀ D f y s := by
  obtain ⟨x, hx, hp⟩ := hp
  exact ⟨x, hx, sncWeightProfiles_scale cX fX d D₀ D x s hp hc⟩

/-- The zero datum is realized over the fibre wherever some datum is. -/
theorem relWeightProfiles_zero (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) (f : X ⟶ Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ relWeightProfiles cX fX d D₀ D f y s) :
    ((0 : ℝ), fun _ => (0 : ℝ)) ∈ relWeightProfiles cX fX d D₀ D f y s := by
  obtain ⟨x, hx, hp⟩ := hp
  exact ⟨x, hx, sncWeightProfiles_zero cX fX d D₀ D x s hp⟩

/-- On a klt pair the first coordinate of a profile datum over the fibre is not negative, and a
datum with first coordinate zero is zero. -/
theorem relWeightProfiles_fst_nonneg (cX : EtaleChart K X n) (fX : X.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ D : CartierDivisor X) (hklt : LogPairIsKlt cX fX d D₀) (f : X ⟶ Y) (y : Y)
    {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) {p : ℝ × (Fin N → ℝ)}
    (hp : p ∈ relWeightProfiles cX fX d D₀ D f y s) :
    0 ≤ p.1 ∧ (p.1 = 0 → ∀ i, p.2 i = 0) := by
  obtain ⟨x, hx, hp⟩ := hp
  exact sncWeightProfiles_fst_nonneg cX fX hd D₀ D hklt x s hp

/-- The specialization comparison over the base from the transfer of rational profiles: if every
rational normalized profile realized over the fibre of y' is realized over the fibre of y, the
infimum over the fibre of y is at most the infimum over the fibre of y'. -/
theorem relWeightInfimum_le_of_rational (cX : EtaleChart K X n) (fX : X.functionFieldˣ) {d : ℕ}
    (hd : 1 ≤ d) (D₀ D : CartierDivisor X) (hklt : LogPairIsKlt cX fX d D₀) (f : X ⟶ Y)
    {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : 0 < j) (t : ℝ) {y y' : Y}
    (hrat : ∀ α : Fin N → ℚ,
      (fun i => (α i : ℝ)) ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y' →
      (fun i => (α i : ℝ)) ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y)
    (hne : (relWeightObjectiveValues cX fX d D₀ D f y' N t j).Nonempty) :
    relWeightInfimum cX fX d D₀ D f y N t j ≤ relWeightInfimum cX fX d D₀ D f y' N t j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  apply le_csInf hne
  rintro val ⟨B, p, hp, rfl⟩
  obtain ⟨hp1, hp0⟩ := relWeightProfiles_fst_nonneg cX fX hd D₀ D hklt f y' B hp
  rcases hp1.lt_or_eq with hp1 | hp1
  · -- a datum with positive first coordinate: approximation by rational profiles
    apply le_of_forall_pos_le_add
    intro ε hε
    have hq : (fun i => p.2 i / p.1) ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y' :=
      ⟨B, p, hp, hp1, fun i => by rw [div_mul_cancel₀ _ hp1.ne']⟩
    obtain ⟨q', hq', hle⟩ := specialization_approximation hj t
      (relWeightNormalizedProfiles cX fX d D₀ D f N y')
      (relWeightNormalizedProfiles cX fX d D₀ D f N y)
      (relWeightNormalizedProfiles_down cX fX d D₀ D f N y') hrat hp1 hq (div_pos hε hNr)
    obtain ⟨B', p', hp', hp'1, hq'p'⟩ := hq'
    have hc : 0 < p.1 / p'.1 := div_pos hp1 hp'1
    have h1 := relWeightInfimum_le cX fX d D₀ D f y t j B'
      (relWeightProfiles_scale cX fX d D₀ D f y B' hp' hc)
    -- the rescaled datum has values at least p₁ q'
    have h2 : (∑ i, Real.exp (p.1 / p'.1 * p'.1 / t - p.1 / p'.1 * p'.2 i / j)) ≤
        ∑ i, Real.exp (p.1 / t - p.1 * q' i / j) := by
      refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_
      rw [div_mul_cancel₀ _ hp'1.ne']
      have h3 : p.1 * q' i ≤ p.1 / p'.1 * p'.2 i := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hp'1]
        have := mul_le_mul_of_nonneg_left (hq'p' i) hp1.le
        linarith
      have h4 : p.1 * q' i / j ≤ p.1 / p'.1 * p'.2 i / j := div_le_div_of_nonneg_right h3 hjr.le
      linarith
    have h5 : (∑ i, Real.exp (p.1 / t - p.1 * q' i / j)) =
        N * minimizationFunctional j t p.1 (fun i => p.1 * q' i) := by
      unfold minimizationFunctional
      field_simp
    have h6 : N * minimizationFunctional j t p.1 (fun i => p.1 * (p.2 i / p.1)) =
        ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
      unfold minimizationFunctional
      have : ∀ i, p.1 * (p.2 i / p.1) = p.2 i := fun i => by field_simp
      simp only [this]
      field_simp
    calc relWeightInfimum cX fX d D₀ D f y N t j
        ≤ ∑ i, Real.exp ((p.1 / p'.1 * p'.1) / t - (p.1 / p'.1 * p'.2 i) / j) := h1
      _ ≤ ∑ i, Real.exp (p.1 / t - p.1 * q' i / j) := h2
      _ = N * minimizationFunctional j t p.1 (fun i => p.1 * q' i) := h5
      _ ≤ N * (minimizationFunctional j t p.1 (fun i => p.1 * (p.2 i / p.1)) + ε / N) :=
        mul_le_mul_of_nonneg_left hle hNr.le
      _ = ∑ i, Real.exp (p.1 / t - p.2 i / j) + ε := by
        rw [mul_add, h6, mul_div_cancel₀ _ hNr.ne']
  · -- the zero datum: the infimum over the fibre of y is at most N
    have hp2 := hp0 hp1.symm
    have hval : (∑ i, Real.exp (p.1 / t - p.2 i / j)) = ∑ _i : Fin N, Real.exp 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hp1, hp2 i, zero_div, zero_div, sub_zero]
    rw [hval]
    by_cases hxne : (relWeightObjectiveValues cX fX d D₀ D f y N t j).Nonempty
    · obtain ⟨_, B₀, p₀, hp₀, -⟩ := hxne
      have h0 := relWeightInfimum_le cX fX d D₀ D f y t j B₀
        (relWeightProfiles_zero cX fX d D₀ D f y B₀ hp₀)
      refine h0.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      simp
    · rw [Set.not_nonempty_iff_eq_empty] at hxne
      unfold relWeightInfimum
      rw [hxne, Real.sInf_empty]
      exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le

/-- The specialization comparison (6) over the base at very general points, from the closedness on
closed points of the realization loci over the base: for w specializing to the closed point y
there are countably many closed sets not containing w outside which the infimum over the fibre of
y is at most the infimum over the fibre of every closed point with a profile datum. -/
theorem relWeight_specialization_comparison_of_closedPoints (cX : EtaleChart K X n)
    (fX : X.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ D : CartierDivisor X)
    (hklt : LogPairIsKlt cX fX d D₀) (f : X ⟶ Y) {N : ℕ} (hN : 0 < N) {j : ℕ} (hj : 0 < j)
    (t : ℝ)
    (hcl : ∀ α : Fin N → ℚ, IsClosedOnClosedPoints {y : Y |
      (fun i => (α i : ℝ)) ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y})
    {w y : Y} (hyc : IsClosed ({y} : Set Y)) (hwy : w ⤳ y) :
    ∃ Z : ℕ → Set Y, (∀ i, IsClosed (Z i)) ∧ (∀ i, w ∉ Z i) ∧
      ∀ y' : Y, IsClosed ({y'} : Set Y) →
        (relWeightObjectiveValues cX fX d D₀ D f y' N t j).Nonempty → (∀ i, y' ∉ Z i) →
        relWeightInfimum cX fX d D₀ D f y N t j ≤ relWeightInfimum cX fX d D₀ D f y' N t j := by
  classical
  choose R hR hrep using hcl
  obtain ⟨e, he⟩ := exists_surjective_nat (Fin N → ℚ)
  refine ⟨fun k => if w ∈ R (e k) then ∅ else R (e k), fun k => ?_, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact isClosed_empty
    · exact hR _
  · dsimp only
    split_ifs with h
    · exact Set.notMem_empty w
    · exact h
  · intro y' hy'c hne hy'Z
    refine relWeightInfimum_le_of_rational cX fX hd D₀ D hklt f hN hj t (fun α hα => ?_) hne
    obtain ⟨k, rfl⟩ := he α
    have hy'R : y' ∈ R (e k) := (hrep (e k) y' hy'c).mp hα
    have hwR : w ∈ R (e k) := by
      by_contra h
      exact hy'Z k (by simpa only [h, ↓reduceIte] using hy'R)
    exact (hrep (e k) y hyc).mpr (hwy.mem_closed (hR _) hwR)

end Definitions

section Specialization

variable {K : Type u} [Field K] {n : ℕ} {X Y : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

/-- On a quasi-compact X, the realization loci over the base are closed on closed points when the
realization loci of the pair on X are and f is a closed map: the closed representative over the
base is the image of the closed representative on X. -/
theorem relWeightNormalizedProfiles_isClosedOnClosedPoints [CompactSpace X]
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor X)
    (f : X ⟶ Y) (hf : IsClosedMap f) (N : ℕ) (α : Fin N → ℚ)
    (hcl : IsClosedOnClosedPoints {x : X |
      (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cX fX d D₀ D N x}) :
    IsClosedOnClosedPoints {y : Y |
      (fun i => (α i : ℝ)) ∈ relWeightNormalizedProfiles cX fX d D₀ D f N y} := by
  obtain ⟨C, hC, hrep⟩ := hcl
  refine ⟨f '' C, hf C hC, fun y hyc => ?_⟩
  have hfib : IsClosed (f ⁻¹' ({y} : Set Y)) := hyc.preimage f.continuous
  constructor
  · intro hα
    obtain ⟨x, hx, hxq⟩ := (mem_relWeightNormalizedProfiles_iff cX fX d D₀ D f N y _).mp hα
    obtain ⟨x', hx'S, hx'c⟩ := ((isClosed_closure (s := ({x} : Set X))).inter
      hfib).exists_closed_singleton ⟨x, subset_closure rfl, hx⟩
    have hxx' : x ⤳ x' := specializes_iff_mem_closure.mpr hx'S.1
    have hq' := sncWeightNormalizedProfiles_of_specializes cX fX d D₀ D N hxx' hxq
    exact ⟨x', (hrep x' hx'c).mp hq', hx'S.2⟩
  · rintro ⟨x, hxC, hxy⟩
    obtain ⟨x', hx'S, hx'c⟩ := (hC.inter hfib).exists_closed_singleton ⟨x, hxC, hxy⟩
    exact (mem_relWeightNormalizedProfiles_iff cX fX d D₀ D f N y _).mpr
      ⟨x', hx'S.2, (hrep x' hx'c).mpr hx'S.1⟩

end Specialization

end MixedFujita
