/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosedPointProfiles

/-!
The klt interior gap from strict lower growth of section dimensions and closed rational-profile
loci. A single good closed point transfers every rational profile at all sufficiently large
degrees. The transfer is independent of t, so the numerical Taylor start at that point supplies
one positive gap on a fixed t-interval for the specified, possibly singular, point.
Closedness itself remains a hypothesis; the numerical start is proved from dimension growth.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
  {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

variable [IsLocallyNoetherian Y]

/-- The klt interior gap at every specified closed point from strict dimension growth and
closed representatives of the rational profile loci at closed points. -/
theorem klt_ample_interior_of_dimension_lower_and_closedPoints (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤
      (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ))
    (hvol : (n : ℝ) / b < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹)
    (hcl : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
        (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) (x : Y) (hxc : IsClosed ({x} : Set Y)) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ δ > 0, ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((j • A).sheaf, ⊤) ∧
      ∀ t, t₀ ≤ t → t ≤ b →
        sncWeightInfimum cY fY d D₀ (j • A) x
          (Module.finrank K Γ((j • A).sheaf, ⊤)) t j ≤
          (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ) * (1 - δ) := by
  obtain ⟨-, -, M, e, he, hbase, -⟩ := id hA
  have : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e hbase
  obtain ⟨y, hycl, hyU, hyD, htransfer⟩ :=
    exists_boundaryFree_closedPoint_all_degree_transfer_of_closedPoints cY fY d D₀ A hcl x hxc
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hstart⟩ :=
    klt_boundaryFree_interior_start_of_dimension_lower hn cY fY d hd D₀ A hklt hA
      hc hb hN hvol y hycl hyU hyD
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) cY.isAffine y hyU hycl
  refine ⟨t₀, ht₀, ht₀b, δ, hδ, ?_⟩
  filter_upwards [htransfer, hstart, hN, eventually_ge_atTop 1] with j hjtr hjstart hjN hj1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hNpos : 0 < Module.finrank K Γ((j • A).sheaf, ⊤) := by
    exact_mod_cast (mul_pos hc (pow_pos hj0 n)).trans_le hjN
  refine ⟨hNpos, ?_⟩
  intro t ht₀t htb
  have ht : 0 < t := ht₀.trans_le ht₀t
  obtain ⟨B, hB⟩ := hjstart t ht₀t htb
  have hne : (sncWeightObjectiveValues cY fY d D₀ (j • A) y
      (Module.finrank K Γ((j • A).sheaf, ⊤)) t j).Nonempty :=
    ⟨_, sncWeightObjectiveValues_natCast_mem cY fY d D₀ (j • A) y B t j⟩
  have hcomp := sncWeightInfimum_le_of_rational cY fY hd D₀ (j • A) hklt hNpos hj1 t hjtr hne
  exact hcomp.trans (sncWeightInfimum_le_of_chart_interior hn cY fY d hd D₀ (j • A)
    hNpos B y hyU β hyD hj1 ht hζ.le hB)


end MixedFujita
