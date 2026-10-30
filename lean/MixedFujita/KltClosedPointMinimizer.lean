/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltClosedPointHyperplane
public import MixedFujita.KltClosedPointInterior
public import MixedFujita.RealizationThresholdReduction
public import MixedFujita.KltNumericalGrowth
public import MixedFujita.RealizationSetsPrincipalShift
public import MixedFujita.HyperplaneSumVeryAmple

/-!
General klt isolation data with the corrected point-closedness hypothesis: the closed
representatives agree with K-valued profile data only at closed points. Membership at generic
points is not imposed. The older full-scheme-closedness implication remains a legacy interface.
A hyperplane representative l*A = J + div(phi), chosen away from x, transports closedness and
restricted growth. The strict volume of A gives the interior gap for J at b = 1/(d*l).
Section 5 then gives point centres, and principal shifts and section powers return data for A.
Smoothness, a numerical-start hypothesis, a Hilbert-limit hypothesis and a point-centre hypothesis
are not required. Closedness itself and Kawamata--Viehweg vanishing remain separate gaps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
  {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The exact K-NF numerical hypotheses and tuple/point closedness imply isolation data at every
closed point and every m₀. Point centres are proved. Point closedness is required only on closed points. -/
theorem klt_ample_minimizerData_of_knf_numerical_and_closedPoints
    (hn : 1 ≤ n) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    (hvol : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ j : ℕ in atTop,
      ((((d * (n + 1) : ℕ) : ℝ) ^ n + ε) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • A) (genericPoint Y)))
    (hsub : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → D' < n → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((((d * (n + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
          cartierRestrictedDim K (j • A) η))
    (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • A) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
        (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) :
    ∀ m₀ : ℕ, 1 ≤ m₀ → KltIsolationMinimizerData cY fY d D₀ A m₀ x := by
  have hdimY : topologicalKrullDim Y = n := etaleChart_topologicalKrullDim cY
  have hgrow := klt_restrictedGrowth_of_knf_numerical (K := K) hdimY A hvol hsub
  obtain ⟨l, hl, M, e, hci, he, g, hg, hggen, hgx, φ, hlA⟩ :=
    cartierIsAmpleProj_exists_hyperplane_nonvanishing hA x
  let J := projectiveHyperplaneCartier e g hg hggen
  have hJ : CartierIsAmpleProj K J := projectiveHyperplaneCartier_isAmpleProj e g hg hggen he
  have htend : Tendsto (fun j : ℕ => j * l) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hl) tendsto_id
  have hclJ : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • J) x := by
    filter_upwards [htend.eventually hclosed] with j hj
    exact realizationSetsZariskiClosed_of_nsmul_eq cY fY d D₀ hlA x j hj
  have hclPtJ : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • J).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • J)
        (Module.finrank K Γ((j • J).sheaf, ⊤)) y} := by
    filter_upwards [htend.eventually hclosedPt] with j hj
    exact normalizedProfiles_closedPoints_of_nsmul_eq cY fY d D₀ hlA j hj
  have hgrowJ : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ∃ V : Submodule K Γ((j • J).sheaf, ⊤), FiniteDimensional K V ∧
          ((((d * l * (n + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
            cartierRestrictedSubspaceDim K (j • J) η V) := by
    intro η D' hD' hD'1 ε hε
    have h := restrictedGrowth_of_nsmul_eq_add_principal A J hl φ hlA η
      (hgrow η D' hD' hD'1) ε hε
    have hconst : (((d * l * (n + 1) : ℕ) : ℝ) ^ D') =
        (l : ℝ) ^ D' * (((d * (n + 1) : ℕ) : ℝ) ^ D') := by
      rw [← mul_pow]
      congr 1
      push_cast
      ring
    rw [hconst]
    exact h
  obtain ⟨ε, hε, hvolA⟩ := hvol
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  let c : ℝ := (l : ℝ) ^ n * ((((d * (n + 1) : ℕ) : ℝ) ^ n) + ε) / n.factorial
  have hc : 0 < c := by dsimp [c]; positivity
  have hNJ : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤
      (Module.finrank K Γ((j • J).sheaf, ⊤) : ℝ) := by
    filter_upwards [htend.eventually hvolA] with j hj
    rw [cartierRestrictedDim_genericPoint] at hj
    rw [finrank_nsmul_eq_of_nsmul_eq (K := K) hlA j]
    convert hj using 1 <;> dsimp [c] <;> push_cast <;> rw [mul_pow] <;> ring
  have hfact : (n.factorial : ℝ) * c = ((d : ℝ) * l * (n + 1)) ^ n + (l : ℝ) ^ n * ε := by
    have hpow : ((d : ℝ) * l * (n + 1)) ^ n =
        (l : ℝ) ^ n * (((d * (n + 1) : ℕ) : ℝ) ^ n) := by
      rw [← mul_pow]
      congr 1
      push_cast
      ring
    rw [hpow]
    dsimp [c]
    field_simp
  have hroot : (d : ℝ) * l * (n + 1) < ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ := by
    rw [hfact, Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hnpos,
      Real.rpow_natCast]
    exact lt_add_of_pos_right _ (mul_pos (pow_pos hlpos n) hε)
  have hthreshold : (n : ℝ) / (1 / ((d : ℝ) * l)) <
      (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ := by
    calc (n : ℝ) / (1 / ((d : ℝ) * l)) = (n : ℝ) / (n + 1) *
          ((d : ℝ) * l * (n + 1)) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hroot (div_pos hnpos (by positivity))
  obtain ⟨t₀, -, ht₀b, δ, hδ, hstart⟩ := klt_ample_interior_of_dimension_lower_and_closedPoints hn cY
    fY d hd D₀ J hklt hJ hc (show 0 < 1 / ((d : ℝ) * l) by positivity) hNJ hthreshold hclPtJ x hxc
  refine klt_projectiveHyperplane_minimizerData_shift_of_closedPoints e g hg hggen he hn cY fY d hd D₀ A
    hklt hl φ hlA x hxc hgx (b := 1 / ((d : ℝ) * l)) (t₀ := t₀) (δ := min δ (1 / 2))
    (by positivity) (by apply le_of_eq; field_simp) (d * l * (n + 1))
    (by have hdl := Nat.mul_le_mul hd hl; simpa using Nat.mul_le_mul hdl (Nat.le_add_left 1 n))
    (by push_cast; field_simp) ht₀b (lt_min hδ (by norm_num))
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) hgrowJ hclJ hclPtJ ?_
  filter_upwards [hstart] with j hj
  intro t ht₀t htb
  exact (hj.2 t ht₀t htb.le).trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_left (min_le_left δ (1 / 2)) 1) (Nat.cast_nonneg _))


/-- The remaining realization-closedness theorem suffices for the full K-NF minimizer statement.
This implication does not assert closedness or Kawamata--Viehweg vanishing. -/
theorem kltMinimizerDataStatement_of_closedPointRealization
    (hclosed : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
      [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
      (n : ℕ) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
      ∀ (D₀ A : CartierDivisor Y), LogPairIsKlt cY fY d D₀ → CartierIsAmpleProj K A →
      ∀ x : Y, IsClosed ({x} : Set Y) →
        (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • A) x) ∧
        (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
          IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
            (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})) :
    KltMinimizerDataStatement.{u} := by
  intro K _ _ _ _ Y _ _ _ _ n hdim hn hnorm hcov cY fY d hd D₀ heff hklt P hA hvol hsub
    m₀ hm₀ x hxc hnotgen
  obtain ⟨hcl, hclPt⟩ := hclosed K Y n cY fY d hd D₀ (d • P - D₀) hklt hA x hxc
  exact klt_ample_minimizerData_of_knf_numerical_and_closedPoints hn cY fY d hd D₀ (d • P - D₀)
    hklt hA hvol hsub x hxc hcl hclPt m₀ hm₀

/-- Lemma 3 at x supplies tuple closedness at all degrees. Only closed-point representatives
are assumed for the point loci; no full-scheme closedness of K-valued profile data is required. -/
theorem klt_ample_minimizerData_of_lemmaThree_and_closedPoints
    (hn : 1 ≤ n) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A)
    (hvol : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ j : ℕ in atTop,
      ((((d * (n + 1) : ℕ) : ℝ) ^ n + ε) * (j : ℝ) ^ n / n.factorial ≤
        cartierRestrictedDim K (j • A) (genericPoint Y)))
    (hsub : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → D' < n → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((((d * (n + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
          cartierRestrictedDim K (j • A) η))
    (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hlct : IdealThresholdZariskiClosed cY fY d D₀ x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ (j • A)
        (Module.finrank K Γ((j • A).sheaf, ⊤)) y}) :
    ∀ m₀ : ℕ, 1 ≤ m₀ → KltIsolationMinimizerData cY fY d D₀ A m₀ x := by
  exact klt_ample_minimizerData_of_knf_numerical_and_closedPoints hn cY fY d hd D₀ A hklt hA
    hvol hsub x hxc (Eventually.of_forall fun j =>
      realizationSetsZariskiClosed_of_idealThreshold cY fY d D₀ x hlct (j • A)) hclosedPt

/-- K-NF from KV and tuple closedness plus closedness of the K-valued point loci only on
closed points. The two closedness assertions and KV are still unproved inputs. -/
theorem kawamataNumericalFreeness_of_kv_of_closedPointRealization
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hclosed : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
      [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
      (n : ℕ) (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ), 1 ≤ d →
      ∀ (D₀ A : CartierDivisor Y), LogPairIsKlt cY fY d D₀ → CartierIsAmpleProj K A →
      ∀ x : Y, IsClosed ({x} : Set Y) →
        (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • A) x) ∧
        (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
          IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
            (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})) :
    KawamataNumericalFreeness.{u} :=
  kawamataNumericalFreeness_of_kawamataViehweg_of_minimizerData hKV
    (kltMinimizerDataStatement_of_closedPointRealization hclosed)

end MixedFujita
