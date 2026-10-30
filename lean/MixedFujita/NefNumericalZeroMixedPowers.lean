/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNumericalDimension
public import MixedFujita.GeneralNefMixedEuler

/-! 元nef数値次元0と全正混合冪交点数消滅の同値。 See reports/check-266-restricted-numerical-zero-center.json for the verified scope. Noetherian minimization over ALL effective lc pairs preserving all-large ORIGINAL L-adjoint ampleness yields an ACTUAL minimal lc center whose naturally restricted ORIGINAL L has numerical dimension ZERO for every ample center polarization and actual pullback representative. Positive original numerical klt BPF data supply the initial pair internally, without an initial L section or KV. This constructs the numerical-zero endpoint, not its nonvanishing, original mL lifting, general KV, the original nu=0 branch, BPF or full F1/F2. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable


/-- For an ORIGINAL nef divisor, numerical dimension zero is equivalent to
vanishing of EVERY positive original ordinary mixed power, not an Iitaka or
section-growth replacement. The converse uses the literal finite maximum;
the forward direction also uses general nef mixed nonnegativity. -/
theorem proper_nef_cartierNumericalDimension_zero_iff_positive_mixed_powers_vanish
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (L J : CartierDivisor X) (hL : CartierIsNef K L) (hJ : CartierIsAmpleProj K J) :
    cartierNumericalDimension K n hdim L J = 0 ↔
      ∀ k : Fin (n + 1), 1 ≤ k.val → cartierMixedPowerIntersection K n hdim L J k = 0 := by
  constructor
  · intro hzero k hk
    have hnonneg : 0 ≤ cartierMixedPowerIntersection K n hdim L J k := by
      unfold cartierMixedPowerIntersection
      apply proper_nef_cartierMixedIntersection_nonneg K ⟨J, hJ⟩
      · have hlen : (List.replicate k.val L ++ List.replicate (n - k.val) J).length = n := by
          simp only [List.length_append, List.length_replicate]
          omega
        intro hnil
        have he := congrArg List.length hnil
        simp only [List.length_nil, hlen] at he
        omega
      · intro D hD
        rcases List.mem_append.mp hD with hD | hD
        · rw [List.eq_of_mem_replicate hD]
          exact hL
        · rw [List.eq_of_mem_replicate hD]
          exact cartierIsAmpleProj_isNef hJ
    apply le_antisymm ?_ hnonneg
    by_contra hnot
    have hpos : 0 < cartierMixedPowerIntersection K n hdim L J k := by omega
    have hmem : k ∈ ((Finset.univ : Finset (Fin (n + 1))).filter fun k =>
        0 < cartierMixedPowerIntersection K n hdim L J k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩
    have hle : k.val ≤ cartierNumericalDimension K n hdim L J := Finset.le_sup (f := Fin.val) hmem
    rw [hzero] at hle
    omega
  · intro hzero
    apply Nat.eq_zero_of_le_zero
    apply Finset.sup_le
    intro k hk
    have hpos := (Finset.mem_filter.mp hk).2
    by_contra hnot
    have hz := hzero k (by omega)
    rw [hz] at hpos
    exact lt_irrefl 0 hpos

end MixedFujita
