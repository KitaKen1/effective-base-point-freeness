/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierBaseLocus
public import MixedFujita.CoprimeAmpleNumericalBound
public import Mathlib.Order.OrderIsoNat

/-! Noether安定化・互いに素な二底から全大倍数生成。 See reports/check-243-base-locus-SNC-cut-basepoint-removal.json for the verified scope. Actual original Cartier base loci stabilize along powers. Stable-locus point removal for two coprime bases implies all large multiples generated. Usual KV lifts actual SNC-roundup cut generators and removes original basepoints. Usual KV and existence of required SNC data and cut generator remain explicit inputs; full klt BPF and F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Base loci along powers of any natural integer form an antitone sequence. -/
theorem cartierBaseLocus_pow_antitone {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) (p : ℕ) : Antitone (fun e : ℕ => cartierBaseLocus ((p ^ e) • D)) := by
  intro e f hef
  exact cartierBaseLocus_le_of_dvd D (pow_dvd_pow p hef)


/-- Noetherianity supplies permanent stability beyond any prescribed starting degree. -/
theorem cartierBaseLocus_pow_stabilizes {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (D : CartierDivisor X) (p e₀ : ℕ) :
    ∃ e : ℕ, e₀ ≤ e ∧ ∀ f : ℕ, e ≤ f →
      cartierBaseLocus ((p ^ f) • D) = cartierBaseLocus ((p ^ e) • D) := by
  obtain ⟨e, he⟩ := WellFoundedLT.antitone_chain_condition (cartierBaseLocus_pow_antitone D p)
  refine ⟨max e e₀, le_max_right _ _, fun f hf => ?_⟩
  exact (he f ((le_max_left _ _).trans hf)).symm.trans (he (max e e₀) (le_max_left _ _))


/-- To get a generated power it suffices to remove one point from each nonempty stable
base locus. The exponent bound and stabilization are supplied internally by Noetherianity. -/
theorem cartier_exists_generated_power_of_stable_base_locus_removal
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (D : CartierDivisor X) (p e₀ : ℕ)
    (hremove : ∀ e : ℕ, e₀ ≤ e →
      (∀ f : ℕ, e ≤ f → cartierBaseLocus ((p ^ f) • D) = cartierBaseLocus ((p ^ e) • D)) →
      (cartierBaseLocus ((p ^ e) • D) : Set X).Nonempty →
        ∃ (f : ℕ) (x : X), e ≤ f ∧ x ∈ cartierBaseLocus ((p ^ e) • D) ∧
          x ∉ cartierBaseLocus ((p ^ f) • D)) :
    ∃ e : ℕ, e₀ ≤ e ∧ CartierIsGloballyGenerated ((p ^ e) • D) := by
  obtain ⟨e, he, hstable⟩ := cartierBaseLocus_pow_stabilizes D p e₀
  refine ⟨e, he, (cartierBaseLocus_eq_bot_iff _).mp ?_⟩
  apply SetLike.ext
  intro x
  change (x ∈ cartierBaseLocus ((p ^ e) • D)) ↔ False
  refine ⟨fun hx => ?_, False.elim⟩
  obtain ⟨f, y, hef, hy, hyn⟩ := hremove e he hstable ⟨x, hx⟩
  exact hyn ((hstable f hef).symm ▸ hy)


/-- Two coprime generated degrees suffice for every large degree, with an explicit
product bound, without ampleness, properness, a field or any vanishing assumption. -/
theorem cartier_coprime_generated_degrees_all_large
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X)
    (m q : ℕ) (hm : 1 ≤ m) (hcop : Nat.Coprime m q)
    (hM : CartierIsGloballyGenerated (m • D)) (hQ : CartierIsGloballyGenerated (q • D)) :
    ∀ j : ℕ, m * q ≤ j → CartierIsGloballyGenerated (j • D) := by
  intro j hj
  obtain ⟨a, b, hab, -⟩ := exists_coprime_representation hm hcop hj
  have h := cartierIsGloballyGenerated_add _ _
    (cartierIsGloballyGenerated_nsmul _ hM a) (cartierIsGloballyGenerated_nsmul _ hQ b)
  have he : a • (m • D) + b • (q • D) = j • D := by
    rw [← mul_nsmul', ← mul_nsmul', ← add_nsmul, hab]
  rwa [he] at h


/-- The end of the X-method needs only stable-base-locus removal for TWO coprime bases.
All topology and the passage from two powers to all large original Cartier multiples are internal. -/
theorem cartier_eventually_generated_of_two_stable_base_locus_removals
    {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    (D : CartierDivisor X) (p q e₀ : ℕ) (hp : 1 ≤ p) (hcop : Nat.Coprime p q)
    (hremove : ∀ b ∈ ({p, q} : Set ℕ), ∀ e : ℕ, e₀ ≤ e →
      (∀ f : ℕ, e ≤ f → cartierBaseLocus ((b ^ f) • D) = cartierBaseLocus ((b ^ e) • D)) →
      (cartierBaseLocus ((b ^ e) • D) : Set X).Nonempty →
        ∃ (f : ℕ) (x : X), e ≤ f ∧ x ∈ cartierBaseLocus ((b ^ e) • D) ∧
          x ∉ cartierBaseLocus ((b ^ f) • D)) :
    ∃ q₀ : ℕ, ∀ j : ℕ, q₀ ≤ j → CartierIsGloballyGenerated (j • D) := by
  obtain ⟨e, -, he⟩ := cartier_exists_generated_power_of_stable_base_locus_removal D p e₀
    (hremove p (by simp))
  obtain ⟨f, -, hf⟩ := cartier_exists_generated_power_of_stable_base_locus_removal D q e₀
    (hremove q (by simp))
  exact ⟨p ^ e * q ^ f, cartier_coprime_generated_degrees_all_large D _ _ (one_le_pow₀ hp)
    (hcop.pow e f) he hf⟩

end MixedFujita
