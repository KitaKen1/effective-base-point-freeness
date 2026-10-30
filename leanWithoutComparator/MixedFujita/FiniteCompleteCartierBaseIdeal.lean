/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionBaseIdeal
public import MixedFujita.CartierBaseLocus
public import Hironaka.Scheme.BlowUp.InvertibleSheaf

/-! 実零Cartier単位イデアルと完全基底集合を保つ有限非零部分系。 See reports/check-248-high-power-lc-perturbation-complete-base.json for the verified scope. One high residual-power Bertini cut constructs an original effective lc non-klt perturbation klt outside the complete base locus, from one initial nonzero section and a nonempty base. SNC principalization, nonzero fixed part, residual generation, threshold, power and original section descent are internal. A nonempty reduced lower-dimensional non-klt W is internally placed inside that complete base locus without KV. Initial and restricted-section nonvanishing, automatic perturbed adjoint nef-big conditions, usual KV, klt BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
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




/-- The zero effective Cartier divisor has the actual unit ideal sheaf. -/
theorem effectiveCartierIdealSheaf_zero_eq_top
    {X : Scheme.{u}} [IsIntegral X] (h0 : (0 : CartierDivisor X).IsEffective) :
    effectiveCartierIdealSheaf (0 : CartierDivisor X) h0 = ⊤ := by
  classical
  choose U hx using fun x : X => Scheme.IdealSheafData.exists_affineOpens_mem x
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ ?_
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    let : Nonempty (U x).1 := ⟨⟨x, hx x⟩⟩
    have hu : regularEquationRationalUnit X (U x).1 1 one_ne_zero = 1 := by
      apply Units.ext
      simp only [regularEquationRationalUnit_val, map_one, Units.val_one]
    have he : rationalUnitClass X (U x).1
        (Additive.ofMul (regularEquationRationalUnit X (U x).1 1 one_ne_zero)) =
        (0 : CartierDivisor X) |_ (U x).1 := by
      rw [hu]
      change rationalUnitClass X (U x).1 0 = _
      simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]
    rw [effectiveCartierIdealSheaf_ideal_eq_span _ h0 (U x) 1 one_ne_zero he]
    simp


/-- Noetherian compactness chooses a finite NONZERO actual subsystem with exactly
the COMPLETE Cartier base locus. A single initial nonzero section prevents an empty family. -/
theorem exists_finite_nonzero_Cartier_subsystem_same_complete_base_locus
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))]
    (M : CartierDivisor X) (s₀ : Γ(M.sheaf, ⊤)) (hs₀ : s₀ ≠ 0) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ (s : Fin r → Γ(M.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0),
      (cartierSectionBaseIdeal M s hs).support = cartierBaseLocus M := by
  classical
  let S := {s : Γ(M.sheaf, ⊤) // s ≠ 0}
  obtain ⟨V, hV⟩ := (NoetherianSpace.isCompact (cartierGenerationOpen M : Set X)).elim_finite_subcover
    (fun j : S => (cartierSectionNonvanishingOpen M j.1 : Set X))
    (fun j => (cartierSectionNonvanishingOpen M j.1).isOpen) (by
      intro x hx
      obtain ⟨s, hs⟩ := (mem_cartierGenerationOpen_iff M x).mp hx
      have hn : s ≠ 0 := (cartierSectionNonvanishingOpen_nonempty_iff M s).mp ⟨⟨x, hs⟩⟩
      exact Set.mem_iUnion.mpr ⟨⟨s, hn⟩, hs⟩)
  let W : Finset S := insert ⟨s₀, hs₀⟩ V
  let : Nonempty W := ⟨⟨⟨s₀, hs₀⟩, Finset.mem_insert_self _ _⟩⟩
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  let s (i : Fin (Fintype.card W)) : Γ(M.sheaf, ⊤) := (e i).1.1
  have hs (i : Fin (Fintype.card W)) : s i ≠ 0 := (e i).1.2
  refine ⟨Fintype.card W, Fintype.card_pos, s, hs, ?_⟩
  apply SetLike.ext
  intro x
  change x ∈ ((cartierSectionBaseIdeal M s hs).support : Set X) ↔ _
  rw [cartierSectionBaseIdeal_support (K := K), Set.mem_iInter]
  change (∀ i, x ∉ cartierSectionNonvanishingOpen M (s i)) ↔ x ∉ cartierGenerationOpen M
  constructor
  · intro hx hgen
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hV hgen)
    obtain ⟨hjV, hjx⟩ := Set.mem_iUnion.mp hj
    have hjW : j ∈ W := Finset.mem_insert_of_mem hjV
    obtain ⟨i, hi⟩ := e.surjective ⟨j, hjW⟩
    apply hx i
    change x ∈ (cartierSectionNonvanishingOpen M (s i) : Set X)
    simpa only [s, hi] using hjx
  · intro hx i hi
    exact hx ((mem_cartierGenerationOpen_iff M x).mpr ⟨s i, hi⟩)

end MixedFujita
