/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.OriginalFiniteSubsystemLCPerturbation
public import MixedFujita.CenterPreservingLinearCombination
public import MixedFujita.AmpleIdealExactBaseLocus

/-! 零切断除去と全高次ampleの中心制限保持・外部lc。 See reports/check-263-exterior-lc-concentration.json for the verified scope. Actual SNC principalization of the SAME original finite subsystem and boundary-avoiding first-nonzero residual Bertini are assembled internally. Fixed-part coefficients vanish at EVERY prime relevant to points outside actual center support. Old LC coefficient bounds and new reduced-cut coefficients 0/1 prove original all-model pointwise exterior LC. Zero sections are filtered while preserving original nonzero indices. ALL high ample powers preserve nonzero natural restriction up to nonzero scalar and prove exterior LC. Positive RESTRICTED numerical dimension gives all-high actual concentrated original lifts preserving exact restricted order AND exterior LC. No original klt, normality, supplied model, initial L section or KV is required. Ambient nonLC from restricted concentration, actual lower-center iteration, original mL/center adjoint vanishing, nu=0, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Remove zero members of a finite family while retaining ORIGINAL indices;
every original nonzero member still occurs. No linear algebra is needed. -/
theorem finite_family_exists_nonzero_index_subfamily
    {V : Type*} [Zero V] (k : ℕ) (s : Fin k → V) :
    ∃ (r : ℕ) (e : Fin r → Fin k), (∀ i, s (e i) ≠ 0) ∧
      ∀ j, s j ≠ 0 → ∃ i, e i = j := by
  classical
  let S := {j : Fin k // s j ≠ 0}
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i => (e i).val, fun i => (e i).property, ?_⟩
  intro j hj
  refine ⟨(Fintype.equivFin S) ⟨j, hj⟩, ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨j, hj⟩)


/-- An ORIGINAL concentrated lift and an actual ideal-zero finite family
spanning off the center give an ORIGINAL nonzero perturbing section with
EXACT scalar restriction and lc outside the center. Zero-family filtering,
SNC principalization and the SAME-subsystem residual Bertini are internal.
The center may be nonreduced, nonintegral or nonnormal. -/
theorem exists_center_preserving_section_logCanonical_outside_center
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D)
    (P : CartierDivisor X) (I : X.IdealSheafData)
    [I.subscheme.Over (Spec (CommRingCat.of K))] [I.subschemeι.IsOver (Spec (CommRingCat.of K))]
    (s₀ : Γ(P.sheaf, ⊤)) (h₀ : modulePullbackGlobalSections I.subschemeι P.sheaf s₀ ≠ 0)
    (k : ℕ) (s : Fin k → Γ(P.sheaf, ⊤))
    (hzero : ∀ i, modulePullbackGlobalSections I.subschemeι P.sheaf (s i) = 0)
    (hunit : ∀ x : X, x ∉ I.support → ∃ i, IsUnit (cartierLocalCoefficient P x
      (Classical.choose (P.exists_isLocalEquationAt x))
      (Classical.choose_spec (P.exists_isLocalEquationAt x)) (s i)))
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ (t : Γ(P.sheaf, ⊤)) (ht : t ≠ 0) (a : K), a ≠ 0 ∧
      modulePullbackGlobalSections I.subschemeι P.sheaf t =
        a • modulePullbackGlobalSections I.subschemeι P.sheaf s₀ ∧
      modulePullbackGlobalSections I.subschemeι P.sheaf t ≠ 0 ∧
      ∀ x : X, x ∉ I.support → LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d)
        (j • D + cartierSectionZeroDivisor P t ht) := by
  classical
  obtain ⟨r, e, he, hcover⟩ := finite_family_exists_nonzero_index_subfamily k s
  let s' : Fin r → Γ(P.sheaf, ⊤) := fun i => s (e i)
  let v : Fin (r + 1) → Γ(P.sheaf, ⊤) := Fin.cons s₀ s'
  have hs₀ : s₀ ≠ 0 := by
    intro h
    apply h₀
    rw [h, map_zero]
  have hv : ∀ i, v i ≠ 0 := by
    intro i
    exact Fin.cases hs₀ (fun l => he l) i
  have hbase : ((cartierSectionBaseIdeal P v hv).support : Set X) ⊆ I.support := by
    intro x hx
    by_contra hn
    obtain ⟨i, hi⟩ := hunit x hn
    have hsi : s i ≠ 0 := (cartierLocalCoefficient_ne_zero_iff P x _ _ _).mp hi.ne_zero
    obtain ⟨l, hl⟩ := hcover i hsi
    rw [cartierSectionBaseIdeal_support (K := K), Set.mem_iInter] at hx
    have hz := hx l.succ
    change x ∈ cartierSectionZeroLocus P (s (e l)) at hz
    rw [hl] at hz
    exact hz ((mem_cartierSectionNonvanishingOpen_iff_localCoefficient P (s i) x _ _).mpr hi)
  obtain ⟨a, ha, ht, hlc'⟩ := exists_original_finite_combination_lc_outside_base c f d hd D hlc
    P r v hv I.support hbase j hj
  let t := ∑ i, a i • v i
  have hres : modulePullbackGlobalSections I.subschemeι P.sheaf t =
      a 0 • modulePullbackGlobalSections I.subschemeι P.sheaf s₀ :=
    fixed_first_linear_combination_natural_restriction I.subschemeι P.sheaf r s₀ s'
      (fun i => hzero (e i)) a
  refine ⟨t, ht, a 0, ha, hres, ?_, hlc'⟩
  rw [hres]
  exact smul_ne_zero ha h₀


/-- ALL high ample powers internally supply the ideal-zero finite family and
an ORIGINAL section preserving any specified nonzero natural restriction up
to a nonzero scalar, with lc perturbation outside the actual center. -/
theorem all_high_ample_exists_center_preserving_lc_exterior_section
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hlc : LogPairIsLogCanonical c f d D)
    (A : CartierDivisor X) (hA : CartierIsAmpleProj K A) (I : X.IdealSheafData)
    [I.subscheme.Over (Spec (CommRingCat.of K))] [I.subschemeι.IsOver (Spec (CommRingCat.of K))] :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ s₀ : Γ((b • A).sheaf, ⊤),
      modulePullbackGlobalSections I.subschemeι (b • A).sheaf s₀ ≠ 0 →
      ∀ j : ℕ, 1 ≤ j → ∃ (t : Γ((b • A).sheaf, ⊤)) (ht : t ≠ 0) (a : K), a ≠ 0 ∧
        modulePullbackGlobalSections I.subschemeι (b • A).sheaf t =
          a • modulePullbackGlobalSections I.subschemeι (b • A).sheaf s₀ ∧
        modulePullbackGlobalSections I.subschemeι (b • A).sheaf t ≠ 0 ∧
        ∀ x : X, x ∉ I.support → LogPairIsLogCanonicalOverBasePoint (𝟙 X) x c f (j * d)
          (j • D + cartierSectionZeroDivisor (b • A) t ht) := by
  obtain ⟨b₀, hb₀⟩ := ample_ideal_finite_sections_common_zero_locus_exact_support A hA I
  refine ⟨b₀, fun b hb s₀ hs₀ j hj => ?_⟩
  obtain ⟨k, s, hzero, hunit, _⟩ := hb₀ b hb
  exact exists_center_preserving_section_logCanonical_outside_center c f d hd D hlc (b • A) I
    s₀ hs₀ k s hzero hunit j hj

end MixedFujita
