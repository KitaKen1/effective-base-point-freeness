/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltVolumeInterior
public import MixedFujita.ProjectiveAmpleMinimizerData

/-!
The exact K-NF numerical hypotheses give restricted subspaces with the growth used by section 5.
A point with full-dimensional closure is the generic point. Its growth comes from the strict
volume input; smaller closures use the proper-subvariety input. No Hilbert limit is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- In a finite-dimensional integral scheme, a point with full-dimensional closure is generic.
The proof appends the ambient irreducible closed set to every chain in a proper closed subset. -/
theorem eq_genericPoint_of_topologicalKrullDim_closure_eq {Y : Scheme.{u}} [IsIntegral Y]
    {n : ℕ} (hdim : topologicalKrullDim Y = n) (η : Y)
    (hη : topologicalKrullDim (closure ({η} : Set Y)) = n) : η = genericPoint Y := by
  by_contra hne
  have hproper : closure ({η} : Set Y) ≠ Set.univ := by
    intro h
    exact hne ((show IsGenericPoint η Set.univ from h).eq (genericPoint_spec Y))
  let Z := closure ({η} : Set Y)
  have : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨Set.univ, by
      have : IrreducibleSpace Z := Subtype.irreducibleSpace isIrreducible_singleton.closure
      exact IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
  let f : IrreducibleCloseds Z → IrreducibleCloseds Y :=
    IrreducibleCloseds.map Subtype.val continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  let U : IrreducibleCloseds Y :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
  have hftop : ∀ C : IrreducibleCloseds Z, f C < U := by
    intro C
    refine lt_iff_le_not_ge.mpr ⟨Set.subset_univ _, fun h => hproper ?_⟩
    have hsub : (f C : Set Y) ⊆ Z := by
      exact closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.property) isClosed_closure
    exact Set.eq_univ_of_univ_subset (Set.Subset.trans h hsub)
  have hsm : StrictMono (WithTop.recTopCoe U f) :=
    WithTop.strictMono_iff.mpr ⟨hf, hftop⟩
  have hle := Order.krullDim_le_of_strictMono _ hsm
  rw [Order.krullDim_WithTop] at hle
  change topologicalKrullDim Z + 1 ≤ topologicalKrullDim Y at hle
  rw [hdim, hη] at hle
  have : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by simpa using hle
  have : n + 1 ≤ n := by exact_mod_cast this
  omega

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Strict generic volume and the K-NF proper-subvariety bounds supply section-5 growth at all
positive-dimensional closures. The chosen subspaces are actual finite-dimensional subspaces. -/
theorem klt_restrictedGrowth_of_knf_numerical
    {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] {n d : ℕ} (hdim : topologicalKrullDim Y = n)
    (A : CartierDivisor Y)
    (hvol : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ j : ℕ in atTop,
      ((((d * (n + 1) : ℕ) : ℝ) ^ n + ε) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • A) (genericPoint Y)))
    (hsub : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → D' < n → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((((d * (n + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
          cartierRestrictedDim K (j • A) η)) :
    ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ∃ V : Submodule K Γ((j • A).sheaf, ⊤), FiniteDimensional K V ∧
          ((((d * (n + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
            cartierRestrictedSubspaceDim K (j • A) η V) := by
  intro η D' hD' hD'1 ε hε
  have hle : D' ≤ n := by
    have h := topologicalKrullDim_subspace_le Y (closure ({η} : Set Y))
    rw [hD', hdim] at h
    exact_mod_cast h
  have hgrow : ∀ᶠ j : ℕ in atTop,
      ((((d * (n + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
        cartierRestrictedDim K (j • A) η) := by
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact hsub η D' hD' hD'1 hlt ε hε
    · have hη := eq_genericPoint_of_topologicalKrullDim_closure_eq hdim η hD'
      obtain ⟨δ, hδ, hvol⟩ := hvol
      filter_upwards [hvol] with j hj
      rw [hη]
      refine le_trans ?_ hj
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) (by positivity)
  filter_upwards [hgrow] with j hj
  obtain ⟨V, hV, hdimV⟩ := exists_finiteDimensional_le_cartierRestrictedSubspaceDim (K := K) (j • A) η
  exact ⟨V, hV, hj.trans (by exact_mod_cast hdimV)⟩

end MixedFujita
