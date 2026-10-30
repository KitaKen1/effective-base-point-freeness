/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveChartSectionExtension
public import MixedFujita.CartierGlobalGenerationOperations

/-! 元Cartier完全線形系の実基底集合と整除包含。 See reports/check-243-base-locus-SNC-cut-basepoint-removal.json for the verified scope. Actual original Cartier base loci stabilize along powers. Stable-locus point removal for two coprime bases implies all large multiples generated. Usual KV lifts actual SNC-roundup cut generators and removes original basepoints. Usual KV and existence of required SNC data and cut generator remain explicit inputs; full klt BPF and F1/F2 remain unproved. -/

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


/-- The actual open where some global section generates the original Cartier sheaf. -/
noncomputable def cartierGenerationOpen {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) : X.Opens :=
  ⨆ s : Γ(D.sheaf, ⊤), cartierSectionNonvanishingOpen D s


/-- The actual closed base locus of the complete original Cartier linear system. -/
noncomputable def cartierBaseLocus {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) : Closeds X := (cartierGenerationOpen D).compl


/-- Membership in the generated open is witnessed by an actual global section. -/
theorem mem_cartierGenerationOpen_iff {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) (x : X) :
    x ∈ cartierGenerationOpen D ↔ ∃ s : Γ(D.sheaf, ⊤), x ∈ cartierSectionNonvanishingOpen D s :=
  Opens.mem_iSup


/-- The closed base locus is exactly the locus where every section fails to generate. -/
theorem mem_cartierBaseLocus_iff {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) (x : X) :
    x ∈ cartierBaseLocus D ↔ ∀ s : Γ(D.sheaf, ⊤), x ∉ cartierSectionNonvanishingOpen D s := by
  change x ∉ cartierGenerationOpen D ↔ _
  rw [mem_cartierGenerationOpen_iff]
  simp only [not_exists]


/-- Empty actual base locus is equivalent to the unchanged original generation predicate. -/
theorem cartierBaseLocus_eq_bot_iff {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) : cartierBaseLocus D = ⊥ ↔ CartierIsGloballyGenerated D := by
  constructor
  · intro h x
    have hx : x ∉ cartierBaseLocus D := by
      intro hx
      rw [h] at hx
      exact hx
    have hx' : x ∈ cartierGenerationOpen D := by
      change ¬ ¬ x ∈ cartierGenerationOpen D at hx
      exact not_not.mp hx
    obtain ⟨s, hs⟩ := (mem_cartierGenerationOpen_iff D x).mp hx'
    exact ⟨s, (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x _ _).mp hs⟩
  · intro h
    apply SetLike.ext
    intro x
    change (x ∈ cartierBaseLocus D) ↔ False
    refine ⟨fun hx => ?_, False.elim⟩
    obtain ⟨s, hs⟩ := h x
    exact (mem_cartierBaseLocus_iff D x).mp hx s
      ((mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x _ _).mpr hs)


/-- A nonzero section is equivalent to the generic point avoiding the actual base locus. -/
theorem genericPoint_not_mem_cartierBaseLocus_iff {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) : genericPoint X ∉ cartierBaseLocus D ↔
      ∃ s : Γ(D.sheaf, ⊤), s ≠ 0 := by
  change (¬ genericPoint X ∉ cartierGenerationOpen D) ↔ _
  rw [not_not, mem_cartierGenerationOpen_iff]
  exact exists_congr fun s => cartierSectionNonvanishingOpen_genericPoint_iff D s


/-- Passing to any natural multiple can only shrink the actual closed base locus. -/
theorem cartierBaseLocus_nsmul_le {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) (k : ℕ) : cartierBaseLocus (k • D) ≤ cartierBaseLocus D := by
  intro x hx
  apply (mem_cartierBaseLocus_iff D x).mpr
  intro s hs
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  have hu := (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x f hf).mp hs
  have hpow : x ∈ cartierSectionNonvanishingOpen (k • D) (cartierSectionPower D s k) := by
    rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x (f ^ k)
      (cartierLocalEquation_pow D x f hf k), cartierSectionPower_localCoefficient]
    exact hu.pow k
  exact (mem_cartierBaseLocus_iff (k • D) x).mp hx _ hpow


/-- Divisibility of actual degrees reverses the inclusion of complete-system base loci. -/
theorem cartierBaseLocus_le_of_dvd {X : Scheme.{u}} [IsIntegral X]
    (D : CartierDivisor X) {m q : ℕ} (hmq : m ∣ q) :
    cartierBaseLocus (q • D) ≤ cartierBaseLocus (m • D) := by
  obtain ⟨k, rfl⟩ := hmq
  simpa only [smul_smul, Nat.mul_comm] using cartierBaseLocus_nsmul_le (m • D) k

end MixedFujita
