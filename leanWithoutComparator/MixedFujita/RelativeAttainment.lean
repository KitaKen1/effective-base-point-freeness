/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasisAttainment
public import MixedFujita.KltAffineLemmaThreeRealization
public import MixedFujita.RelativeWeightProfiles

/-!
Attainment of the minimum over the fibre (step 17R-2, section 3.2 of the manuscript relative to
f).

The attainment of section 3.2 uses the closedness of the realization sets at the point only to
find one basis realizing a whole increasing sequence of rational profiles. Over a fibre the
realizations may happen at different points of the fibre, and the projection of the realization
sets along the fibre is not used. Instead:

* `exists_basis_profile_minimizer_of_common`: the abstract attainment theorem with a family of
  realization relations indexed by points, assuming that an increasing sequence of rational
  profiles realized at some points by some parameters is realized at one point by one parameter;
* `exists_common_realization_point_klt`: this holds for the realizations of a klt pair at the closed
  points of a quasi-compact set of X. On a finite cover by affine opens with local equations, the
  pairs (closed point, coefficient matrix) realizing a rational profile are the zero sets of
  ideals of Γ(V)[c] (the klt Lemma 3, `exists_ideal_realization_on_affine_klt`); the partial sums
  of these ideals increase, hence stabilize, and a realization at the stable level is a common
  one;
* `rel_exists_basis_sncWeightProfile_minimizer`: the infimum over all bases and all profile data
  over the fibre of a closed point y of the base is attained, under the uniform bounds below a
  level and the interior condition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology Set
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

section Abstract

variable {Θ ι : Type*}

/-- Attainment of the minimum over all parameters (abstract form of section 3.2 with realizations
at varying points): the closedness of the realization sets is replaced by the existence of a
common realization of increasing sequences of rational profiles. -/
theorem exists_basis_profile_minimizer_of_common {N : ℕ} (hN : 0 < N) {t j : ℝ} (ht : 0 < t)
    (hj : 0 < j) (G : Set Θ) (P : Θ → Set (ℝ × (Fin N → ℝ))) (F : Set ι)
    (R : ι → Θ → (Fin N → ℝ) → Prop)
    (hcommon : ∀ α : ℕ → Fin N → ℚ, (∀ l i, 0 ≤ α l i) → (∀ l i, α l i ≤ α (l + 1) i) →
      (∀ l, ∃ x ∈ F, ∃ c ∈ G, R x c (fun i => (α l i : ℝ))) →
      ∃ x ∈ F, ∃ c ∈ G, ∀ l, R x c (fun i => (α l i : ℝ)))
    (hreal : ∀ c ∈ G, ∀ p ∈ P c, 0 < p.1 → ∀ α : Fin N → ℝ, (∀ i, 0 ≤ α i) →
      (∀ i, α i = 0 ∨ α i * p.1 < p.2 i) → ∃ x ∈ F, R x c α)
    (hlimit : ∀ x ∈ F, ∀ c ∈ G, ∀ (α : ℕ → Fin N → ℝ) (q : Fin N → ℝ), (∀ l i, 0 ≤ α l i) →
      (∀ l, R x c (α l)) → Tendsto α atTop (𝓝 q) → (∃ i, 0 < q i) →
      ∃ v : Fin N → ℝ, ((1 : ℝ), v) ∈ P c ∧ ∀ i, q i ≤ v i)
    (hscale : ∀ c ∈ G, ∀ p ∈ P c, ∀ lam : ℝ, 0 ≤ lam →
      (lam * p.1, fun i => lam * p.2 i) ∈ P c)
    {L aLow aHigh Cq : ℝ} (haLow : 0 < aLow)
    (hbd : ∀ c ∈ G, ∀ p ∈ P c, (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ L →
      aLow ≤ p.1 ∧ p.1 ≤ aHigh ∧ ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ Cq * p.1)
    (hint : ∃ c ∈ G, ∃ p ∈ P c, (∑ i, Real.exp (p.1 / t - p.2 i / j)) < L ∧
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) < N) :
    ∃ c ∈ G, ∃ p ∈ P c, ∀ c' ∈ G, ∀ p' ∈ P c',
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j) := by
  classical
  set Φ : ℝ × (Fin N → ℝ) → ℝ := fun p => ∑ i, Real.exp (p.1 / t - p.2 i / j) with hΦ
  set S : Set ℝ := {y | ∃ c ∈ G, ∃ p ∈ P c, Φ p = y} with hS
  obtain ⟨c₀, hc₀, p₀, hp₀, hp₀L, hp₀N⟩ := hint
  have hSne : S.Nonempty := ⟨Φ p₀, c₀, hc₀, p₀, hp₀, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by
    rintro y ⟨c, hc, p, hp, rfl⟩
    exact Finset.sum_nonneg fun i _ => (Real.exp_pos _).le⟩
  have hfle : sInf S ≤ Φ p₀ := csInf_le hSbdd ⟨c₀, hc₀, p₀, hp₀, rfl⟩
  have hfL : sInf S < L := lt_of_le_of_lt hfle hp₀L
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sInf hSne hSbdd
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hu.eventually (gt_mem_nhds hfL))
  -- the data of the minimizing sequence
  have hdata : ∀ k, ∃ c ∈ G, ∃ p ∈ P c, Φ p = u (k + k₀) := fun k => huS (k + k₀)
  choose cs hcs ps hps hΦps using hdata
  have hbdk : ∀ k, aLow ≤ (ps k).1 ∧ (ps k).1 ≤ aHigh ∧
      ∀ i, 0 ≤ (ps k).2 i ∧ (ps k).2 i ≤ Cq * (ps k).1 := fun k =>
    hbd (cs k) (hcs k) (ps k) (hps k) (by
      change Φ (ps k) ≤ L
      rw [hΦps k]
      exact (hk₀ (k + k₀) (Nat.le_add_left _ _)).le)
  have hapos : ∀ k, 0 < (ps k).1 := fun k => haLow.trans_le (hbdk k).1
  -- the normalized values lie in a box
  have hqs : ∀ k i, (ps k).2 i / (ps k).1 ∈ Icc (0 : ℝ) Cq := fun k i =>
    ⟨div_nonneg ((hbdk k).2.2 i).1 (hapos k).le, by
      rw [div_le_iff₀ (hapos k)]
      exact ((hbdk k).2.2 i).2⟩
  have hbox : IsCompact (Icc aLow aHigh ×ˢ Set.pi univ (fun _ : Fin N => Icc (0 : ℝ) Cq)) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨⟨a₀, q⟩, hmem, φ, hφ, hlim⟩ := hbox.tendsto_subseq
    (x := fun k => ((ps k).1, fun i => (ps k).2 i / (ps k).1))
    (fun k => ⟨⟨(hbdk k).1, (hbdk k).2.1⟩, fun i _ => hqs k i⟩)
  have ha₀pos : 0 < a₀ := haLow.trans_le hmem.1.1
  have hq0 : ∀ i, 0 ≤ q i := fun i => (hmem.2 i (mem_univ i)).1
  have hlim_q : Tendsto (fun k => fun i => (ps (φ k)).2 i / (ps (φ k)).1) atTop (𝓝 q) :=
    (continuous_snd.tendsto _).comp hlim
  -- the objective at the limit is the infimum
  set Ψ : ℝ × (Fin N → ℝ) → ℝ := fun p => ∑ i, Real.exp (p.1 / t - p.1 * p.2 i / j) with hΨ
  have hΨcont : Continuous Ψ := by
    rw [hΨ]
    fun_prop
  have hΨk : ∀ k, Ψ ((ps k).1, fun i => (ps k).2 i / (ps k).1) = u (k + k₀) := by
    intro k
    rw [← hΦps k]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : (ps k).1 ≠ 0 := (hapos k).ne'
    have h : (ps k).1 * ((ps k).2 i / (ps k).1) = (ps k).2 i := by field_simp
    change Real.exp ((ps k).1 / t - (ps k).1 * ((ps k).2 i / (ps k).1) / j) = _
    rw [h]
  have hΨlim : Ψ (a₀, q) = sInf S := by
    have h1 : Tendsto (fun k => Ψ ((ps (φ k)).1, fun i => (ps (φ k)).2 i / (ps (φ k)).1)) atTop
        (𝓝 (Ψ (a₀, q))) := (hΨcont.tendsto (a₀, q)).comp hlim
    have h2 : Tendsto (fun k => u (φ k + k₀)) atTop (𝓝 (sInf S)) :=
      hu.comp ((tendsto_add_atTop_nat k₀).comp hφ.tendsto_atTop)
    exact tendsto_nhds_unique (h1.congr fun k => hΨk (φ k)) h2
  -- some limit value is positive
  have hqpos : ∃ i, 0 < q i := by
    by_contra hno
    push Not at hno
    have hq0' : ∀ i, q i = 0 := fun i => le_antisymm (hno i) (hq0 i)
    have hval : Ψ (a₀, q) = N * Real.exp (a₀ / t) := by
      change (∑ i, Real.exp (a₀ / t - a₀ * q i / j)) = _
      simp only [hq0', mul_zero, zero_div, sub_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hexp : 1 < Real.exp (a₀ / t) := Real.one_lt_exp_iff.mpr (div_pos ha₀pos ht)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hfN : sInf S < N := lt_of_le_of_lt hfle hp₀N
    rw [hΨlim] at hval
    nlinarith
  -- rational profiles increasing to q, realized at some points by some parameters
  obtain ⟨α, hα0, hαmono, hαlt, hαlim⟩ := exists_monotone_rational_lower_approximation q hq0
  have hne : ∀ l, ∃ x ∈ F, ∃ c ∈ G, R x c (fun i => (α l i : ℝ)) := by
    intro l
    have hev : ∀ᶠ k in atTop, ∀ i, (α l i : ℝ) = 0 ∨
        (α l i : ℝ) < (ps (φ k)).2 i / (ps (φ k)).1 := by
      rw [eventually_all]
      intro i
      rcases hαlt l i with h0 | hlt
      · exact Eventually.of_forall fun k => Or.inl (by exact_mod_cast h0)
      · exact ((tendsto_pi_nhds.mp hlim_q i).eventually (lt_mem_nhds hlt)).mono
          fun k hk => Or.inr hk
    obtain ⟨k, hk⟩ := hev.exists
    obtain ⟨x, hx, hR⟩ := hreal (cs (φ k)) (hcs (φ k)) (ps (φ k)) (hps (φ k)) (hapos (φ k))
      (fun i => (α l i : ℝ)) (fun i => by exact_mod_cast hα0 l i) fun i => by
        rcases hk i with h0 | hlt
        · exact Or.inl h0
        · exact Or.inr ((lt_div_iff₀ (hapos (φ k))).mp hlt)
    exact ⟨x, hx, cs (φ k), hcs (φ k), hR⟩
  -- a common realization and the limit datum on it
  obtain ⟨xstar, hxF, cstar, hcG, hRstar⟩ := hcommon α hα0 hαmono hne
  obtain ⟨v, hv, hvq⟩ := hlimit xstar hxF cstar hcG (fun l i => (α l i : ℝ)) q
    (fun l i => by exact_mod_cast hα0 l i) hRstar hαlim hqpos
  have hsc := hscale cstar hcG (1, v) hv a₀ ha₀pos.le
  refine ⟨cstar, hcG, (a₀ * 1, fun i => a₀ * v i), hsc, fun c' hc' p' hp' => ?_⟩
  have h1 : (∑ i, Real.exp ((a₀ * 1) / t - a₀ * v i / j)) ≤ Ψ (a₀, q) := by
    refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_
    have h : a₀ * q i / j ≤ a₀ * v i / j :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hvq i) ha₀pos.le) hj.le
    rw [mul_one]
    linarith
  have h2 : sInf S ≤ Φ p' := csInf_le hSbdd ⟨c', hc', p', hp', rfl⟩
  rw [hΨlim] at h1
  exact h1.trans h2

end Abstract

section Common

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

omit [IsAlgClosed K] [CharZero K] [IsLocallyNoetherian X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))] in
/-- Realization at a point gives realization at its specializations. -/
theorem isRealizedProfile_of_specializes (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor X) {x x' : X} (hxx' : x ⤳ x') {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    {α : Fin N → ℝ} (h : IsRealizedProfile cX fX d D₀ D x s α) :
    IsRealizedProfile cX fX d D₀ D x' s α := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, hval⟩ := h
  exact ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hxx'.mem_closed isClosed_closure hcl,
    hpos, hval⟩

/-- A common realization at closed points of a quasi-compact set: if every rational profile of an
increasing sequence is realized at some closed point of F by the tuple of some coefficient matrix
in G, then one closed point of F and one coefficient matrix in G realize all of them. -/
theorem exists_common_realization_point_klt (hL3 : KltAffineLemmaThreeStatement K) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D₀) (hklt : LogPairIsKlt cX fX d D₀)
    (D : CartierDivisor X) {N m : ℕ} (b : Fin m → Γ(D.sheaf, ⊤)) (F : Set X) (hF : IsCompact F)
    (G : Set (Fin N × Fin m → K)) (α : ℕ → Fin N → ℚ) (hα0 : ∀ l i, 0 ≤ α l i)
    (hαmono : ∀ l i, α l i ≤ α (l + 1) i)
    (hne : ∀ l, ∃ x ∈ {x ∈ F | IsClosed ({x} : Set X)}, ∃ c ∈ G,
      IsRealizedProfile cX fX d D₀ D x (fun i => ∑ k, c (i, k) • b k) (fun i => (α l i : ℝ))) :
    ∃ x ∈ {x ∈ F | IsClosed ({x} : Set X)}, ∃ c ∈ G, ∀ l,
      IsRealizedProfile cX fX d D₀ D x (fun i => ∑ k, c (i, k) • b k) (fun i => (α l i : ℝ)) := by
  classical
  -- the profiles increase with the level
  have hle : ∀ {l l' : ℕ}, l ≤ l' → ∀ i, ((α l i : ℚ) : ℝ) ≤ α l' i := by
    intro l l' h i
    have hmono : Monotone (fun l => α l i) := monotone_nat_of_le_succ fun l => hαmono l i
    exact_mod_cast hmono h
  -- affine charts with local equations and regular sections around each point
  have hchart : ∀ x : X, ∃ (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
      (f : X.functionFieldˣ) (r : Fin m → Γ(X, V)),
      (∀ y ∈ V, D.IsLocalEquationAt y f) ∧ ∀ (_ : Nonempty V), ∀ k,
        X.germToFunctionField V (r k) = (f : X.functionField) * cartierSectionRational D (b k) := by
    intro x
    obtain ⟨V, hV, hxV, f, r, e₀, h, hloc, -, hr⟩ :=
      exists_affine_localEquation_regular_pair (0 : CartierDivisor X)
        CartierDivisor.isEffective_zero D x b
    exact ⟨V, hV, hxV, f, r, hloc, fun hVne => (hr hVne).1⟩
  choose V hV hxV f r hloc hr using hchart
  -- a finite subcover of F
  obtain ⟨s, hs⟩ := hF.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  -- the ideals of the realization sets on the charts
  have hI : ∀ (x : X) (l : ℕ), ∃ I : Ideal (MvPolynomial (Fin N × Fin m) Γ(X, V x)),
      ∀ (y : X) (hy : y ∈ V x), IsClosed ({y} : Set X) → ∀ c : Fin N × Fin m → K,
        (IsRealizedProfile cX fX d D₀ D y (fun i => ∑ k, c (i, k) • b k)
            (fun i => (α l i : ℝ)) ↔
          ∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(X, V x) (c i)) g ∈
            ((hV x).primeIdealOf ⟨y, hy⟩).asIdeal) := by
    intro x l
    have hVne : Nonempty (V x) := ⟨⟨x, hxV x⟩⟩
    exact exists_ideal_realization_on_affine_klt hL3 hn hnorm hcov cX fX hd D₀ heff hklt D b
      (α l) (hα0 l) (V x) (hV x) (f x) (r x) (hloc x) (hr x hVne)
  choose I hIspec using hI
  -- the partial sums of the ideals stabilize
  have hnoeth : ∀ x : X, IsNoetherianRing (MvPolynomial (Fin N × Fin m) Γ(X, V x)) := by
    intro x
    have : IsNoetherianRing Γ(X, V x) :=
      IsLocallyNoetherian.component_noetherian ⟨V x, hV x⟩
    infer_instance
  let S : ∀ x : X, ℕ →o Ideal (MvPolynomial (Fin N × Fin m) Γ(X, V x)) := fun x =>
    ⟨fun l => ⨆ l' ∈ Finset.range (l + 1), I x l', fun l l' h =>
      iSup₂_mono' fun l₁ hl₁ => ⟨l₁, by
        rw [Finset.mem_range] at hl₁ ⊢
        omega, le_rfl⟩⟩
  have hstab : ∀ x : X, ∃ l₀, ∀ l, l₀ ≤ l → S x l₀ = S x l := fun x =>
    (monotone_stabilizes_iff_noetherian (R := MvPolynomial (Fin N × Fin m) Γ(X, V x))).mpr
      (hnoeth x) (S x)
  choose l₀ hl₀ using hstab
  -- a realization at the stable level is a common one
  let L : ℕ := s.sup l₀
  obtain ⟨x₁, ⟨hx₁F, hx₁c⟩, c₁, hc₁G, hR₁⟩ := hne L
  obtain ⟨z, hzs, hx₁z⟩ : ∃ z ∈ s, x₁ ∈ V z := by
    have h := hs hx₁F
    simp only [Set.mem_iUnion] at h
    obtain ⟨z, hzs, hz⟩ := h
    exact ⟨z, hzs, hz⟩
  set Q : Ideal (MvPolynomial (Fin N × Fin m) Γ(X, V z)) := Ideal.comap
    (MvPolynomial.eval (fun i => algebraMap K Γ(X, V z) (c₁ i)))
    ((hV z).primeIdealOf ⟨x₁, hx₁z⟩).asIdeal with hQ
  have hcrit : ∀ l', IsRealizedProfile cX fX d D₀ D x₁ (fun i => ∑ k, c₁ (i, k) • b k)
      (fun i => (α l' i : ℝ)) ↔ I z l' ≤ Q := by
    intro l'
    rw [hIspec z l' x₁ hx₁z hx₁c c₁]
    exact ⟨fun h g hg => Ideal.mem_comap.mpr (h g hg), fun h g hg => Ideal.mem_comap.mp (h hg)⟩
  have hSL : S z L ≤ Q := by
    apply iSup₂_le
    intro l' hl'
    rw [Finset.mem_range] at hl'
    exact (hcrit l').mp (isRealizedProfile_antitone cX fX d D₀ D x₁ _
      (fun i => hle (by omega) i) hR₁)
  refine ⟨x₁, ⟨hx₁F, hx₁c⟩, c₁, hc₁G, fun l => ?_⟩
  by_cases hl : l ≤ L
  · exact isRealizedProfile_antitone cX fX d D₀ D x₁ _ (fun i => hle hl i) hR₁
  · push Not at hl
    have hl₀L : l₀ z ≤ L := Finset.le_sup hzs
    have hSl : S z (l₀ z) = S z l := hl₀ z l (by omega)
    have hSl₀ : S z (l₀ z) ≤ S z L := (S z).monotone hl₀L
    have hIl : I z l ≤ S z l :=
      le_iSup₂_of_le l (Finset.self_mem_range_succ l) le_rfl
    exact (hcrit l).mpr (hIl.trans (hSl ▸ hSl₀.trans hSL))

end Common

section Fibre

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- Attainment of the minimum of the objective over all bases of the sections of D and all profile
data over the fibre of a closed point y of the base, from the uniform bounds below a level and the
interior condition (the klt Lemma 3 supplies the common realizations). -/
theorem rel_exists_basis_sncWeightProfile_minimizer [CompactSpace X]
    (hL3 : KltAffineLemmaThreeStatement K) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) {d : ℕ} (hd : 1 ≤ d) (D₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective cX fX d D₀) (hklt : LogPairIsKlt cX fX d D₀)
    (D : CartierDivisor X) (f : X ⟶ Y) (y : Y) (hyc : IsClosed ({y} : Set Y)) {N : ℕ}
    (hN : 0 < N) (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) {t j : ℝ} (ht : 0 < t)
    (hj : 0 < j) {L aLow aHigh Cq : ℝ} (haLow : 0 < aLow)
    (hbd : ∀ (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)),
      ∀ p ∈ relWeightProfiles cX fX d D₀ D f y B, (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ L →
        aLow ≤ p.1 ∧ p.1 ≤ aHigh ∧ ∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ Cq * p.1)
    (hint : ∃ (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)),
      ∃ p ∈ relWeightProfiles cX fX d D₀ D f y B, (∑ i, Real.exp (p.1 / t - p.2 i / j)) < L ∧
        (∑ i, Real.exp (p.1 / t - p.2 i / j)) < N) :
    ∃ (B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)), ∃ p ∈ relWeightProfiles cX fX d D₀ D f y B,
      ∀ (B' : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)),
        ∀ p' ∈ relWeightProfiles cX fX d D₀ D f y B',
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j) := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hfin : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis b₀
  have hcard : Fintype.card (Fin N) = Module.finrank K Γ(D.sheaf, ⊤) :=
    (Module.finrank_eq_card_basis b₀).symm
  have hfib : IsClosed (f ⁻¹' ({y} : Set Y)) := hyc.preimage f.continuous
  -- the tuple of a coefficient matrix
  set tup : (Fin N × Fin N → K) → Fin N → Γ(D.sheaf, ⊤) :=
    fun c i => ∑ k, c (i, k) • b₀ k with htup
  have hbasis : ∀ c : Fin N × Fin N → K, LinearIndependent K (tup c) →
      ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤), ⇑B = tup c := fun c hc =>
    ⟨basisOfLinearIndependentOfCardEqFinrank hc hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank hc hcard⟩
  have hcoord : ∀ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      ∃ c : Fin N × Fin N → K, LinearIndependent K (tup c) ∧ tup c = ⇑B := by
    intro B
    have h : tup (fun ik => b₀.repr (B ik.1) ik.2) = ⇑B := by
      funext i
      exact b₀.sum_repr (B i)
    exact ⟨fun ik => b₀.repr (B ik.1) ik.2, by rw [h]; exact B.linearIndependent, h⟩
  obtain ⟨c, hcG, p, hp, hmin⟩ := exists_basis_profile_minimizer_of_common hN ht hj
    {c : Fin N × Fin N → K | LinearIndependent K (tup c)}
    (fun c => relWeightProfiles cX fX d D₀ D f y (tup c))
    {x : X | x ∈ f ⁻¹' ({y} : Set Y) ∧ IsClosed ({x} : Set X)}
    (fun x c α => IsRealizedProfile cX fX d D₀ D x (tup c) α)
    (fun α hα0 hαmono hne => exists_common_realization_point_klt hL3 hn hnorm hcov cX fX hd D₀
      heff hklt D b₀ (f ⁻¹' ({y} : Set Y)) hfib.isCompact _ α hα0 hαmono hne)
    (by
      rintro c - p ⟨x, hxy, hp⟩ hp1 α - hα
      obtain ⟨hs, X', hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX', r, ξ, w, hinj, hξ, hsnc,
        hBsupp, hGsupp, hw0, hwΦ, hA, hv⟩ := hp
      have hR := isRealizedProfile_of_sncWeight π hπ cX fX d hd D₀ cX' ξ hinj hξ hsnc hBsupp D
        (tup c) hs hGsupp x w hw0 hwΦ (by rw [← hA]; exact hp1) (fun i => by
          rw [← hA, ← hv i]
          exact hα i)
      -- a closed point of the fibre in the closure of x
      obtain ⟨x', hx'S, hx'c⟩ := ((isClosed_closure (s := ({x} : Set X))).inter
        hfib).exists_closed_singleton ⟨x, subset_closure rfl, hxy⟩
      exact ⟨x', ⟨hx'S.2, hx'c⟩, isRealizedProfile_of_specializes cX fX d D₀ D
        (specializes_iff_mem_closure.mpr hx'S.1) (tup c) hR⟩)
    (by
      rintro x ⟨hxy, -⟩ c hc α q hα0 hreal hlim hqpos
      have hs : ∀ i, tup c i ≠ 0 := fun i => LinearIndependent.ne_zero i hc
      obtain ⟨X', hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX', r, ξ, hinj, hξ, hsnc, hBsupp,
        hGsupp⟩ := exists_proper_snc_model_with cX fX d D₀
          (fun i => cartierSectionZeroDivisor D (tup c i) (hs i))
      obtain ⟨u, hu0, huΦ, huA, huv⟩ := exists_normalized_sncWeight_of_tendsto_isRealizedProfile π
        hπ cX fX d hd D₀ hklt cX' ξ hinj hξ hsnc hBsupp D (tup c) hs hGsupp x α q hα0 hreal hlim
        hqpos
      exact ⟨fun i => ∑ k, u k * (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor D (tup c i) (hs i))) (ξ k) : ℝ),
        ⟨x, hxy, hs, X', hXi, inferInstance, hXo, hXs, π, hπd, hπo, hπp, hπ, cX', r, ξ, u, hinj,
          hξ, hsnc, hBsupp, hGsupp, hu0, huΦ, huA.symm, fun i => rfl⟩, huv⟩)
    (fun c _ p ⟨x, hxy, hp⟩ lam hlam =>
      ⟨x, hxy, sncWeightProfiles_smul cX fX d D₀ D x (tup c) hp hlam⟩)
    haLow
    (by
      intro c hc p hp hL
      obtain ⟨B, hB⟩ := hbasis c hc
      exact hbd B p (by rw [hB]; exact hp) hL)
    (by
      obtain ⟨B, p, hp, h1, h2⟩ := hint
      obtain ⟨c, hcG, hc⟩ := hcoord B
      exact ⟨c, hcG, p, by rw [hc]; exact hp, h1, h2⟩)
  obtain ⟨B, hB⟩ := hbasis c hcG
  refine ⟨B, p, by rw [hB]; exact hp, fun B' p' hp' => ?_⟩
  obtain ⟨c', hc'G, hc'⟩ := hcoord B'
  exact hmin c' hc'G p' (by rw [hc']; exact hp')

end Fibre

end MixedFujita
