/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeFibreCentre
public import MixedFujita.RelativeLemmaTwo
public import MixedFujita.RelativeInteriorStart
public import MixedFujita.KltClosedPointMinimizer
public import MixedFujita.KltFibreRestriction
public import MixedFujita.KltLemmaThreeFromSpecialization

/-!
The existence of the data of the minimizer for relative K-NF (step 17R-2): `RelMinimizerDataStatement`
holds (`relMinimizerDataStatement_holds`), hence relative K-NF holds, and F2 follows from the base
point free theorem for klt pairs alone.

The proof is that of `klt_ample_minimizerData_of_knf_numerical_and_closedPoints` over the fibre of
the closed point y of the base:

* the numerics of L on the base give the restricted growth of L, a hyperplane representative
  l L = J + div φ not through y, and the growth of the sections of j J;
* the klt Lemma 3 on X gives the closedness on closed points of the rational realization loci of
  the pair for the sections of every divisor of X, in particular of j f*J;
* the interior gap over the fibre (`rel_klt_ample_interior_of_dimension_lower_and_closedPoints`);
* Lemma 1 and Lemma 2 over the fibre, the attainment over the fibre and the fibre-centre property
  along a degree sequence realizing the liminf of the normalized infimum over the fibre
  (`rel_klt_projectiveHyperplane_exists_minimal_fibreCentre`), with the specialization
  comparison (6) over the base from the closedness (`rel_klt_projectiveHyperplane_exists_fibreCentre_of_closedPoints`);
* the principal shift to L and the powers of the sections
  (`rel_klt_projectiveHyperplane_minimizerData_shift_of_closedPoints`).
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

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The klt Lemma 3 on affine opens (from the specialization of bad points in smooth families). -/
theorem kltAffineLemmaThreeStatement_proved (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] :
    KltAffineLemmaThreeStatement K :=
  kltAffineLemmaThreeStatement_of_familySpecialization
    (kltFamilySpecializationStatement_of_product kltProductGenericRestrictionStatement_holds
      (kltProductFibreRestrictionStatement_holds K))

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {N n : ℕ}
  {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))] [IsProper f]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

set_option quotPrecheck false

local notation "J" => projectiveHyperplaneCartier e g hg hggen
local notation "Nsec" =>
  (fun j : ℕ => Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤))

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian Y] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] [IsProper f]
  [IsAlgClosed K] [CharZero K] [Uncountable K] in
/-- The sections of the multiples of the pullback of the hyperplane class are finite-dimensional
and as many as on the base, and there are some. -/
theorem rel_projectiveHyperplane_sections
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
    [hfin : ∀ j : ℕ, FiniteDimensional K Γ((j • J).sheaf, ⊤)] (y : Y) :
    (∀ j : ℕ, FiniteDimensional K Γ((j • cartierPullback f J).sheaf, ⊤)) ∧
      (∀ j : ℕ, Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤) =
        Module.finrank K Γ((j • J).sheaf, ⊤)) ∧
      ∀ j : ℕ, 0 < Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤) := by
  have hrank : ∀ j : ℕ, Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤) =
      Module.finrank K Γ((j • J).sheaf, ⊤) := fun j =>
    stein_finrank_sections_nsmul_cartierPullback f happ K J j
  refine ⟨fun j => ?_, hrank, fun j => ?_⟩
  · rw [← cartierPullback_nsmul]
    exact LinearEquiv.finiteDimensional (steinCartierSectionEquiv f K happ (j • J))
  · rw [hrank j]
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen y j
    have hσ₀0 : σ₀ ≠ 0 := by
      rintro rfl
      obtain ⟨φ, hφ, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 y).mp hσ₀
      rw [map_zero] at hu
      exact not_isUnit_zero hu
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, hσ₀0⟩

variable [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- A minimizing profile datum over the fibre of y with the fibre-centre property, for the
pullback of a hyperplane class of the base, conditional on the interior gap over the fibre, the
specialization comparison over the base and the degree conditions of the base. -/
theorem rel_klt_projectiveHyperplane_exists_minimal_fibreCentre
    (hL3 : KltAffineLemmaThreeStatement K)
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D₀) (hklt : LogPairIsKlt cX fX d D₀)
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ} (hk : 1 ≤ k)
    (hdimY : topologicalKrullDim Y = k) (y : Y) (hyc : IsClosed ({y} : Set Y))
    (hgy : g ∉ (e y).asHomogeneousIdeal)
    {b t₀ δ : ℝ} (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s) (hsb : (s : ℝ) * b = k + 1) (ht₀ : t₀ < b)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdim : ∀ w : Y, w ⤳ y → ∃ D' : ℕ, D' ≤ k ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ y → w ≠ y →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun j : ℕ => (Module.finrank K
          Γ((j • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (j : ℝ) ^ D') atTop (𝓝 ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y (Nsec j) t j ≤
        (Nsec j : ℝ) * (1 - δ))
    (h6 : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b → ∀ w : Y, w ⤳ y → w ≠ y →
      ∃ G : Set Y, ClosedPointsDenseOver K w G ∧
        ∀ y' : Y, IsClosed ({y'} : Set Y) → y' ∈ G → w ⤳ y' →
          relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y (Nsec j) t j ≤
            relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y' (Nsec j) t j) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ j : ℕ, 1 ≤ j ∧ 0 < Nsec j ∧
      ∃ B : Module.Basis (Fin (Nsec j)) K Γ((j • cartierPullback f J).sheaf, ⊤),
        ∃ p ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B,
          (∀ p' ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B,
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) < (Nsec j : ℝ) ∧
          RelWeightProfileHasFibreCentre cX fX d D₀ (j • cartierPullback f J) f y B p := by
  have := cartierIsAmpleProj_isProper_base H hH
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  have hJ : CartierIsAmpleProj K J := projectiveHyperplaneCartier_isAmpleProj e g hg hggen he
  obtain ⟨r₀, hr₀, hfin, hlim⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he
    hdimY hk
  obtain ⟨hfinX, hrank, hNpos⟩ := rel_projectiveHyperplane_sections f e g hg hggen happ y
  have hlimX : Tendsto (fun j : ℕ => (Nsec j : ℝ) / (j : ℝ) ^ k) atTop
      (𝓝 ((r₀ : ℝ) / k.factorial)) := by
    refine hlim.congr fun j => ?_
    change (Module.finrank K Γ((j • J).sheaf, ⊤) : ℝ) / (j : ℝ) ^ k =
      (Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤) : ℝ) / (j : ℝ) ^ k
    rw [hrank j]
  have hν : (0 : ℝ) < (r₀ : ℝ) / k.factorial := by
    have : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
    positivity
  obtain ⟨C, hC, hcoeff⟩ := klt_sncWeightProfiles_lower_bounds hn cX fX d hd D₀
    (cartierPullback f J) hklt hH
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have ha : 0 < -Real.log (1 - δ) / C := by
    have hlog : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
    exact div_pos (by linarith) hCr
  obtain ⟨t, ht₀', ht, htb, hpc⟩ := rel_projectiveHyperplane_fibreCentre_along_sequence_of_dense f
    e g hg hggen he happ f.isClosedMap cX fX hd D₀ hklt y hyc hgy (show 0 < k from hk) ha hb s hs
    hsb ht₀ hdim hdeg
  let F : ℕ → ℝ := fun j => relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y (Nsec j) t j /
    Nsec j
  have hFle : ∀ᶠ j : ℕ in atTop, F j ≤ 1 - δ := by
    filter_upwards [hstart] with j hj
    have hNr : (0 : ℝ) < Nsec j := by exact_mod_cast hNpos j
    exact (div_le_iff₀ hNr).mpr (by simpa [mul_comm] using hj t ht₀' htb)
  -- a point of the fibre and Lemma 2 over the fibre
  obtain ⟨x₀, hx₀⟩ := surjective_of_isProper_of_isDominant f y
  obtain ⟨κ, hκ, -, hev8⟩ := rel_klt_normalizedInfimum_ge hn cX fX d hd D₀ hklt hH f happ hdimY hk
    hJ hb
  have hFge : ∀ᶠ j : ℕ in atTop, κ ≤ F j := by
    filter_upwards [hev8] with j hj
    have h := hj x₀ (hNpos j) (Module.finBasis K _) ht htb.le
    rw [hx₀] at h
    exact h
  have hF0 : ∀ j : ℕ, 0 ≤ F j := fun j =>
    div_nonneg (relWeightInfimum_nonneg cX fX d D₀ _ f y (Nsec j) t j) (Nat.cast_nonneg _)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop F :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hF0)
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop F :=
    isCoboundedUnder_ge_of_eventually_le atTop hFle
  obtain ⟨mseq, hmseqf, hmseq⟩ := exists_seq_tendsto_liminf hcobdd hbdd
  have hcpos : 0 < liminf F atTop := hκ.trans_le (le_liminf_of_le hcobdd hFge)
  -- the minimizers over the fibre and their log discrepancies
  have hevmin := rel_klt_global_minimizer_of_infimum_gap hL3 hn hnorm hcov cX fX d hd D₀ heff hklt
    hH f happ hdimY hk hJ hb
  have hmin : ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Nsec j)) K Γ((j • cartierPullback f J).sheaf, ⊤),
        ∃ p ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B,
          (∀ B' : Module.Basis (Fin (Nsec j)) K Γ((j • cartierPullback f J).sheaf, ⊤),
            ∀ p' ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B',
              (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (Nsec j : ℝ) * (1 - δ) := by
    filter_upwards [hevmin, hstart] with j hjmin hjst
    exact hjmin y hyc (hNpos j) (Module.finBasis K _) ht htb.le hδ
      ⟨_, relWeightObjectiveValues_natCast_mem cX fX d D₀ _ f hx₀ (Module.finBasis K _) t j⟩
      (hjst t ht₀' htb)
  have hAj : ∀ᶠ j : ℕ in atTop,
      ∀ B : Module.Basis (Fin (Nsec j)) K Γ((j • cartierPullback f J).sheaf, ⊤),
        ∀ p ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B,
          (∀ B' : Module.Basis (Fin (Nsec j)) K Γ((j • cartierPullback f J).sheaf, ⊤),
            ∀ p' ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B',
              (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) →
          -Real.log (1 - δ) / C ≤ p.1 := by
    filter_upwards [hmin, eventually_ge_atTop 1] with j hj hj1
    intro B p hp hpmin
    obtain ⟨B₁, p₁, hp₁, -, hp₁val⟩ := hj
    obtain ⟨x, -, hpx⟩ := hp
    exact (hcoeff j hj1 x (hNpos j) B p hpx ht ((hpmin B₁ p₁ hp₁).trans hp₁val)).1
  have hpcev := hpc hν hlimX hcpos rfl hbdd mseq hmseq hmseqf
    (hmseq.eventually (h6.mono fun j hj => hj t ht₀' htb)) (hmseq.eventually hAj)
  obtain ⟨i, hipc, himin, hi1⟩ := (hpcev.and ((hmseq.eventually hmin).and
    (hmseq.eventually (eventually_ge_atTop 1)))).exists
  obtain ⟨B, p, hp, hpmin, hpval⟩ := himin
  have hNr : (0 : ℝ) < Nsec (mseq i) := by exact_mod_cast hNpos (mseq i)
  exact ⟨t, ht₀', ht, htb, mseq i, hi1, hNpos (mseq i), B, p, hp,
    fun p' hp' => hpmin B p' hp', hpval.trans_lt (by nlinarith), hipc B p hp hpmin⟩

/-- The minimizing profile datum over the fibre with the fibre-centre property from the interior
gap, the restricted growth of the hyperplane class on the base and the closedness on closed points
of the realization loci of the pair on X. -/
theorem rel_klt_projectiveHyperplane_exists_fibreCentre_of_closedPoints
    (hL3 : KltAffineLemmaThreeStatement K)
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D₀) (hklt : LogPairIsKlt cX fX d D₀)
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ} (hk : 1 ≤ k)
    (hdimY : topologicalKrullDim Y = k) (y : Y) (hyc : IsClosed ({y} : Set Y))
    (hgy : g ∉ (e y).asHomogeneousIdeal)
    {b t₀ δ : ℝ} (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s) (hsb : (s : ℝ) * b = k + 1) (ht₀ : t₀ < b)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgrow : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ∃ V : Submodule K Γ((j • J).sheaf, ⊤), FiniteDimensional K V ∧
          ((s : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
            cartierRestrictedSubspaceDim K (j • J) η V)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Nsec j) → ℚ,
      IsClosedOnClosedPoints {x : X | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cX fX d D₀ (j • cartierPullback f J) (Nsec j) x})
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y (Nsec j) t j ≤
        (Nsec j : ℝ) * (1 - δ)) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ j : ℕ, 1 ≤ j ∧ 0 < Nsec j ∧
      ∃ B : Module.Basis (Fin (Nsec j)) K Γ((j • cartierPullback f J).sheaf, ⊤),
        ∃ p ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B,
          (∀ p' ∈ relWeightProfiles cX fX d D₀ (j • cartierPullback f J) f y B,
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) < (Nsec j : ℝ) ∧
          RelWeightProfileHasFibreCentre cX fX d D₀ (j • cartierPullback f J) f y B p := by
  have := cartierIsAmpleProj_isProper_base H hH
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hdimY hk
  obtain ⟨hfinX, -, hNpos⟩ := rel_projectiveHyperplane_sections f e g hg hggen happ y
  refine rel_klt_projectiveHyperplane_exists_minimal_fibreCentre f e g hg hggen hL3 he hn hnorm
    hcov cX fX d hd D₀ heff hklt hH happ hk hdimY y hyc hgy hb s hs hsb ht₀ hδ hδ1
    (fun w _ => exists_nat_topologicalKrullDim_closure_eq hdimY w)
    (projectiveHyperplane_degreeCondition_of_restrictedGrowth e g hg hggen he y s hgrow)
    hstart ?_
  -- the specialization comparison (6) over the base
  filter_upwards [hclosedPt, eventually_ge_atTop 1] with j hj hj1
  intro t _ _ w hwy _
  have hrel : ∀ α : Fin (Nsec j) → ℚ, IsClosedOnClosedPoints {y' : Y | (fun i => (α i : ℝ)) ∈
      relWeightNormalizedProfiles cX fX d D₀ (j • cartierPullback f J) f (Nsec j) y'} :=
    fun α => relWeightNormalizedProfiles_isClosedOnClosedPoints cX fX d D₀ _ f f.isClosedMap _ α
      (hj α)
  obtain ⟨Z, hZ, hwZ, hcomp⟩ := relWeight_specialization_comparison_of_closedPoints cX fX hd D₀
    (j • cartierPullback f J) hklt f (hNpos j) hj1 t hrel hyc hwy
  refine ⟨⋂ i, (Z i)ᶜ, closedPointsDenseOver_of_countable Z hZ hwZ, ?_⟩
  intro y' hy'c hy' _
  obtain ⟨x', hx'⟩ := surjective_of_isProper_of_isDominant f y'
  exact hcomp y' hy'c ⟨_, relWeightObjectiveValues_natCast_mem cX fX d D₀ _ f hx'
    (Module.finBasis K _) t j⟩ (Set.mem_iInter.mp hy')

/-- Principal shifts transfer the fibre-centre construction to A. The budget d l b ≤ 1 leaves
strict room at the parameter t < b, and the powers of the sections give every m₀ ≥ 1. -/
theorem rel_klt_projectiveHyperplane_minimizerData_shift_of_closedPoints
    (hL3 : KltAffineLemmaThreeStatement K)
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D₀) (hklt : LogPairIsKlt cX fX d D₀)
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ} (hk : 1 ≤ k)
    (hdimY : topologicalKrullDim Y = k) (A : CartierDivisor Y) {l : ℕ} (hl : 1 ≤ l)
    (φ : Y.functionFieldˣ) (hlA : l • A = J + principalCartierDivisor Y φ)
    (y : Y) (hyc : IsClosed ({y} : Set Y)) (hgy : g ∉ (e y).asHomogeneousIdeal)
    {b t₀ δ : ℝ} (hb : 0 < b) (hbudget : (d : ℝ) * l * b ≤ 1)
    (s : ℕ) (hs : 1 ≤ s) (hsb : (s : ℝ) * b = k + 1) (ht₀ : t₀ < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hgrow : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ∃ V : Submodule K Γ((j • J).sheaf, ⊤), FiniteDimensional K V ∧
          ((s : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
            cartierRestrictedSubspaceDim K (j • J) η V)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Nsec j) → ℚ,
      IsClosedOnClosedPoints {x : X | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cX fX d D₀ (j • cartierPullback f J) (Nsec j) x})
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      relWeightInfimum cX fX d D₀ (j • cartierPullback f J) f y (Nsec j) t j ≤
        (Nsec j : ℝ) * (1 - δ)) :
    ∀ m₀ : ℕ, 1 ≤ m₀ → RelIsolationMinimizerData cX fX d D₀ f A m₀ y := by
  have := cartierIsAmpleProj_isProper_base H hH
  obtain ⟨t, -, ht, htb, j, hj, hN, B, p, hp, hmin, hlt, hpc⟩ :=
    rel_klt_projectiveHyperplane_exists_fibreCentre_of_closedPoints f e g hg hggen hL3 he hn hnorm
      hcov cX fX d hd D₀ heff hklt hH happ hk hdimY y hyc hgy hb s hs hsb ht₀ hδ hδ1 hgrow
      hclosedPt hstart
  have hdl : (0 : ℝ) < (d : ℝ) * l := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    have : (0 : ℝ) < l := by exact_mod_cast hl
    positivity
  have hdt : (d : ℝ) * l * t < 1 :=
    (mul_lt_mul_of_pos_left htb hdl).trans_le hbudget
  have hdata := relIsolationMinimizerData_of_minimal_relWeightProfile_shift cX fX d hd D₀ hklt f
    J A φ hlA y j hj hN B ht hdt hp hmin hlt hpc
  exact fun m₀ hm₀ => relIsolationMinimizerData_of_relIsolationMinimizerData cX fX d D₀ f A y
    hdata m₀ hm₀

end Hyperplane

section Numerical

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {n : ℕ}
  {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The data of the minimizer for relative K-NF at every closed point of the base and every m₀,
from the numerical hypotheses of K-NF for L on the base (with d the index of the pair on X and k
the dimension of the base). -/
theorem rel_klt_ample_minimizerData_of_knf_numerical (hL3 : KltAffineLemmaThreeStatement K)
    (hn : 1 ≤ n) (hdimX : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D₀) (hklt : LogPairIsKlt cX fX d D₀)
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) {k : ℕ} (hk : 1 ≤ k)
    (hdimY : topologicalKrullDim Y = k) (A : CartierDivisor Y) (hA : CartierIsAmpleProj K A)
    (hvol : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ j : ℕ in atTop,
      ((((d * (k + 1) : ℕ) : ℝ) ^ k + ε) * (j : ℝ) ^ k / k.factorial ≤
        cartierRestrictedDim K (j • A) (genericPoint Y)))
    (hsub : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → D' < k → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ((((d * (k + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
          cartierRestrictedDim K (j • A) η))
    (y : Y) (hyc : IsClosed ({y} : Set Y)) :
    ∀ m₀ : ℕ, 1 ≤ m₀ → RelIsolationMinimizerData cX fX d D₀ f A m₀ y := by
  -- properness
  have := cartierIsAmpleProj_isProper_base H hH
  have := cartierIsAmpleProj_isProper_base A hA
  have : IsProper (f ≫ (Y ↘ Spec (CommRingCat.of K))) := by
    rw [HomIsOver.comp_over]
    infer_instance
  have : IsProper f := IsProper.of_comp f (Y ↘ Spec (CommRingCat.of K))
  -- the numerics on the base and a hyperplane representative not through y
  have hgrow := klt_restrictedGrowth_of_knf_numerical (K := K) hdimY A hvol hsub
  obtain ⟨l, hl, M, e, hci, he, g, hg, hggen, hgy, φ, hlA⟩ :=
    cartierIsAmpleProj_exists_hyperplane_nonvanishing hA y
  have hJ : CartierIsAmpleProj K (projectiveHyperplaneCartier e g hg hggen) :=
    projectiveHyperplaneCartier_isAmpleProj e g hg hggen he
  -- closedness of the realization loci on X (the klt Lemma 3)
  have hclPtJ := closedPointRealization_klt hL3 hn hnorm hcov cX fX hd D₀ heff hklt
    (cartierPullback f (projectiveHyperplaneCartier e g hg hggen))
  have hgrowJ : ∀ (η : Y) (D' : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = D' →
      1 ≤ D' → ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
        ∃ V : Submodule K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
          FiniteDimensional K V ∧
          ((((d * l * (k + 1) : ℕ) : ℝ) ^ D' - ε) * (j : ℝ) ^ D' / D'.factorial ≤
            cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V) := by
    intro η D' hD' hD'1 ε hε
    have h := restrictedGrowth_of_nsmul_eq_add_principal A
      (projectiveHyperplaneCartier e g hg hggen) hl φ hlA η (hgrow η D' hD' hD'1) ε hε
    have hconst : (((d * l * (k + 1) : ℕ) : ℝ) ^ D') =
        (l : ℝ) ^ D' * (((d * (k + 1) : ℕ) : ℝ) ^ D') := by
      rw [← mul_pow]
      congr 1
      push_cast
      ring
    rw [hconst]
    exact h
  -- the constants of the interior gap
  obtain ⟨ε, hε, hvolA⟩ := hvol
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  let c : ℝ := (l : ℝ) ^ k * ((((d * (k + 1) : ℕ) : ℝ) ^ k) + ε) / k.factorial
  have hc : 0 < c := by dsimp [c]; positivity
  have htend : Tendsto (fun j : ℕ => j * l) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hl) tendsto_id
  have hNJ : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ k ≤
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by
    filter_upwards [htend.eventually hvolA] with j hj
    rw [cartierRestrictedDim_genericPoint] at hj
    rw [finrank_nsmul_eq_of_nsmul_eq (K := K) hlA j]
    convert hj using 1 <;> dsimp [c] <;> push_cast <;> rw [mul_pow] <;> ring
  have hfact : (k.factorial : ℝ) * c = ((d : ℝ) * l * (k + 1)) ^ k + (l : ℝ) ^ k * ε := by
    have hpow : ((d : ℝ) * l * (k + 1)) ^ k =
        (l : ℝ) ^ k * (((d * (k + 1) : ℕ) : ℝ) ^ k) := by
      rw [← mul_pow]
      congr 1
      push_cast
      ring
    rw [hpow]
    dsimp [c]
    field_simp
  have hroot : (d : ℝ) * l * (k + 1) < ((k.factorial : ℝ) * c) ^ (k : ℝ)⁻¹ := by
    rw [hfact, Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hkpos,
      Real.rpow_natCast]
    exact lt_add_of_pos_right _ (mul_pos (pow_pos hlpos k) hε)
  have hthreshold : (k : ℝ) / (1 / ((d : ℝ) * l)) <
      (k : ℝ) / (k + 1) * ((k.factorial : ℝ) * c) ^ (k : ℝ)⁻¹ := by
    calc (k : ℝ) / (1 / ((d : ℝ) * l)) = (k : ℝ) / (k + 1) *
          ((d : ℝ) * l * (k + 1)) := by field_simp
      _ < _ := mul_lt_mul_of_pos_left hroot (div_pos hkpos (by positivity))
  -- the interior gap over the fibre
  have hclX : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K
      Γ((cartierPullback f (j • projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {x : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cX fX d
        D₀ (cartierPullback f (j • projectiveHyperplaneCartier e g hg hggen)) (Module.finrank K
        Γ((cartierPullback f (j • projectiveHyperplaneCartier e g hg hggen)).sheaf, ⊤)) x} := by
    filter_upwards [hclPtJ] with j hj
    rw [cartierPullback_nsmul]
    exact hj
  obtain ⟨t₀, -, ht₀b, δ, hδ, hstart⟩ := rel_klt_ample_interior_of_dimension_lower_and_closedPoints
    hk hdimX hdimY cX fX d hd D₀ hklt hH f happ (projectiveHyperplaneCartier e g hg hggen) hJ hc
    (show 0 < 1 / ((d : ℝ) * l) by positivity) hNJ hthreshold hclX y hyc
  refine rel_klt_projectiveHyperplane_minimizerData_shift_of_closedPoints f e g hg hggen hL3 he hn
    hnorm hcov cX fX d hd D₀ heff hklt hH happ hk hdimY A hl φ hlA y hyc hgy
    (b := 1 / ((d : ℝ) * l)) (t₀ := t₀) (δ := min δ (1 / 2)) (by positivity)
    (by apply le_of_eq; field_simp) (d * l * (k + 1))
    (by have hdl := Nat.mul_le_mul hd hl; simpa using Nat.mul_le_mul hdl (Nat.le_add_left 1 k))
    (by push_cast; field_simp) ht₀b (lt_min hδ (by norm_num))
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) hgrowJ hclPtJ ?_
  filter_upwards [hstart] with j hj
  intro t ht₀t htb
  have h := hj.2 t ht₀t htb.le
  rw [cartierPullback_nsmul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_left (min_le_left δ (1 / 2)) 1) (Nat.cast_nonneg _))

end Numerical

/-- **The data of the minimizer for relative K-NF exist** (`RelMinimizerDataStatement`). -/
theorem relMinimizerDataStatement_holds : RelMinimizerDataStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D heff hklt Y _ _ _ _ k hdimY hk
    hnormY hcovY f _ _ hfapp P L hL hN hvol hsub m₀ hm₀ y hy hgen
  obtain ⟨H, hH⟩ := hH₀
  exact rel_klt_ample_minimizerData_of_knf_numerical (kltAffineLemmaThreeStatement_proved K) hn
    hdim hnorm hcov c₀ f₀ r hr D heff hklt hH f (fun U => (hfapp U).2) hk hdimY L hL hvol hsub y
    hy m₀ hm₀

/-- **Relative K-NF holds.** -/
theorem relativeNumericalFreeness_proved : RelativeNumericalFreeness.{u} :=
  relativeNumericalFreeness_of_relMinimizerData relMinimizerDataStatement_holds

/-- **F2 from the base point free theorem for klt pairs alone**: neither Ambro's canonical bundle
formula nor Hodge theory is used. -/
theorem linearEffectiveFreeness_of_basePointFree (hbpf : KltBasePointFreeStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_basePointFree_of_relMinimizerData hbpf relMinimizerDataStatement_holds

end MixedFujita
