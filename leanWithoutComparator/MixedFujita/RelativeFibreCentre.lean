/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeCenterDegree
public import MixedFujita.ProjectiveHyperplanePointCentre
public import MixedFujita.RelativeMinimizerAssembly

/-!
The conclusion of section 5 over a fibre (step 17R-2): along a degree sequence realizing the
liminf of the normalized infimum over the fibre of y, the minimizing profile data over the fibre
eventually have the fibre-centre property `RelWeightProfileHasFibreCentre`.

The proof is that of `projectiveHyperplane_pointCentre_along_sequence_of_dense` with the point x
replaced by the fibre of y. A point of a model, not over the fibre, whose closure meets the
preimage of the fibre and whose polytope contains the normalized profile gives a weight with the
same datum; the image in the base of the centre of that weight is a point w ≠ y specializing to y.
The chart data at a general closed point z of the centre are those of the composite ρ = π ≫ f to
the base (`projectiveHyperplane_exists_closedPoint_tangent_chart_dense`), the specialization
comparison (6) over the base compares the infima over the fibres of y and of ρ(z), and the
inequalities of one degree over the fibre (`rel_projectiveHyperplane_centerDegreeInequalities`)
contradict the limit. The number of tangent coordinates is bounded by the dimension of the models,
not by that of the base, so the limit is used with a separate bound for the dimensions of the
centres (`exists_parameter_point_centers_le`).
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

section Limit

/-- (23) with a separate bound for the dimensions of the centres: the inequalities of one degree
are eventually excluded for every dimension from 1 to Dm. -/
theorem eventually_point_centers_of_gap_le (n l Dm : ℕ) (hn : 0 < n) (hl : 2 ≤ l)
    {lam t b a : ℝ} (hlam : 0 < lam) (ht : 0 < t) (htb : t ≤ b) (ha : 0 < a)
    (hgap : 1 / t < lam * uniformGridSum (fun s => s ^ n * Real.exp ((1 - s) * (a / b))) l)
    (N : ℕ → ℕ) {ν : ℝ} (hν : 0 < ν)
    (hN : Tendsto (fun j : ℕ => (N j : ℝ) / (j : ℝ) ^ n) atTop (𝓝 ν))
    (f : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (hliminf : liminf f atTop = c)
    (hbdd : IsBoundedUnder (· ≥ ·) atTop f)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hfm : Tendsto (fun k => f (m k)) atTop (𝓝 c))
    (C : ℕ → ℝ) (M₀ : ℕ → ℕ) (P : ℕ → ℕ → Prop)
    (hdata : ∀ k D, 0 < D → D ≤ Dm → P k D → M₀ D ≤ m k →
      ∃ (Q : ℕ → ℝ) (T A : ℝ), CenterDegreeInequalities N f t lam (C D) a l (m k) D Q T A) :
    ∀ᶠ k in atTop, ∀ D, 0 < D → D ≤ Dm → ¬ P k D := by
  have hall : (∀ᶠ k in atTop, ∀ D ∈ Finset.Icc 1 Dm, ¬ P k D) ↔
      ∀ D ∈ Finset.Icc 1 Dm, ∀ᶠ k in atTop, ¬ P k D := eventually_all_finset _
  suffices h : ∀ D ∈ Finset.Icc 1 Dm, ∀ᶠ k in atTop, ¬ P k D by
    exact (hall.mpr h).mono fun k hk D hD hDn => hk D (Finset.mem_Icc.mpr ⟨hD, hDn⟩)
  intro D hDmem
  obtain ⟨hD, hDn⟩ := Finset.mem_Icc.mp hDmem
  by_contra hfr
  rw [Filter.not_eventually] at hfr
  simp only [not_not] at hfr
  obtain ⟨φ, hφ, hPφ⟩ := Filter.extraction_of_frequently_atTop hfr
  have hmφ : Tendsto (fun k => m (φ k)) atTop atTop := hm.comp hφ.tendsto_atTop
  have hdataφ : ∀ k, ∃ (Q : ℕ → ℝ) (T A : ℝ), M₀ D ≤ m (φ k) →
      CenterDegreeInequalities N f t lam (C D) a l (m (φ k)) D Q T A := by
    intro k
    by_cases hk : M₀ D ≤ m (φ k)
    · obtain ⟨Q, T, A, h⟩ := hdata (φ k) D hD hDn (hPφ k) hk
      exact ⟨Q, T, A, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hk⟩
  choose Q T A hQTA using hdataφ
  exact moving_center_partition_contradiction n l D hn hl hD N hν hN f hc hliminf hbdd
    (fun k => m (φ k)) hmφ (hfm.comp hφ.tendsto_atTop) hlam ht htb ha hgap Q T A
    ((hmφ.eventually (eventually_ge_atTop (M₀ D))).mono fun k hk => hQTA k hk)

/-- (23) for the parameter t chosen in [t₀, b), with a separate bound for the dimensions of the
centres. -/
theorem exists_parameter_point_centers_le (n : ℕ) (hn : 0 < n) {a b lam t₀ : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hlam : lam * b = n + 1) (ht₀ : t₀ < b) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ l : ℕ, 2 ≤ l ∧
      ∀ (Dm : ℕ) (N : ℕ → ℕ) {ν : ℝ}, 0 < ν →
        Tendsto (fun j : ℕ => (N j : ℝ) / (j : ℝ) ^ n) atTop (𝓝 ν) →
      ∀ (f : ℕ → ℝ) {c : ℝ}, 0 < c → liminf f atTop = c → IsBoundedUnder (· ≥ ·) atTop f →
      ∀ (m : ℕ → ℕ), Tendsto m atTop atTop → Tendsto (fun k => f (m k)) atTop (𝓝 c) →
      ∀ (C : ℕ → ℝ) (M₀ : ℕ → ℕ) (P : ℕ → ℕ → Prop),
        (∀ k D, 0 < D → D ≤ Dm → P k D → M₀ D ≤ m k →
          ∃ (Q : ℕ → ℝ) (T A : ℝ), CenterDegreeInequalities N f t lam (C D) a l (m k) D Q T A) →
        ∀ᶠ k in atTop, ∀ D, 0 < D → D ≤ Dm → ¬ P k D := by
  obtain ⟨t, ht₀', ht, htb, l, hl, hgap⟩ := exists_parameter_finite_partition_gap n ha hb hlam ht₀
  have hlampos : 0 < lam := by
    by_contra h
    push Not at h
    have : lam * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hb.le
    have : (0 : ℝ) < n + 1 := by positivity
    linarith
  refine ⟨t, ht₀', ht, htb, l, hl, ?_⟩
  intro Dm N ν hν hN f c hc hliminf hbdd m hm hfm C M₀ P hdata
  exact eventually_point_centers_of_gap_le n l Dm hn hl hlampos ht htb.le ha hgap N hν hN f hc
    hliminf hbdd m hm hfm C M₀ P hdata

end Limit

section FibreCentre

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {N n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

set_option quotPrecheck false

local notation "J" => projectiveHyperplaneCartier e g hg hggen
local notation "Nsec" =>
  (fun j : ℕ => Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤))

/-- The fibre-centre property along a degree sequence realizing the liminf of the normalized
infimum over the fibre of y, for the pullback of the hyperplane class, when the specialization
comparison (6) over the base holds at the closed points of sets whose closed points are dense
over each generization w ≠ y of y, and (6) and the bound a ≤ A of the minimizing profile data
over the fibre are known for the large members of the sequence and the chosen t. -/
theorem rel_projectiveHyperplane_fibreCentre_along_sequence_of_dense
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K))
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom) (hfcl : IsClosedMap f)
    [∀ j : ℕ, FiniteDimensional K Γ((j • J).sheaf, ⊤)]
    [∀ j : ℕ, FiniteDimensional K Γ((j • cartierPullback f J).sheaf, ⊤)]
    {dd k : ℕ} (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (hdd : 1 ≤ dd)
    (D₀ : CartierDivisor X) (hklt : LogPairIsKlt cX fX dd D₀)
    (y : Y) (hyc : IsClosed ({y} : Set Y)) (hgy : g ∉ (e y).asHomogeneousIdeal)
    (hk : 0 < k) {a b t₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s)
    (hsb : (s : ℝ) * b = k + 1) (ht₀ : t₀ < b)
    (hdim : ∀ w : Y, w ⤳ y → ∃ D' : ℕ, D' ≤ k ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ y → w ≠ y →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧
      ∀ {ν c : ℝ}, 0 < ν →
        Tendsto (fun j : ℕ => (Nsec j : ℝ) / (j : ℝ) ^ k) atTop (𝓝 ν) →
        0 < c →
        liminf (fun j : ℕ => relWeightInfimum cX fX dd D₀ (j • cartierPullback f J) f y
          (Nsec j) t j / Nsec j) atTop = c →
        IsBoundedUnder (· ≥ ·) atTop (fun j : ℕ => relWeightInfimum cX fX dd D₀
          (j • cartierPullback f J) f y (Nsec j) t j / Nsec j) →
        ∀ m : ℕ → ℕ, Tendsto m atTop atTop →
        Tendsto (fun i => relWeightInfimum cX fX dd D₀ (m i • cartierPullback f J) f y
          (Nsec (m i)) t (m i) / Nsec (m i)) atTop (𝓝 c) →
        (∀ᶠ i in atTop, ∀ w : Y, w ⤳ y → w ≠ y → ∃ G : Set Y, ClosedPointsDenseOver K w G ∧
          ∀ y' : Y, IsClosed ({y'} : Set Y) → y' ∈ G → w ⤳ y' →
            relWeightInfimum cX fX dd D₀ (m i • cartierPullback f J) f y (Nsec (m i)) t (m i) ≤
              relWeightInfimum cX fX dd D₀ (m i • cartierPullback f J) f y' (Nsec (m i)) t
                (m i)) →
        (∀ᶠ i in atTop, ∀ (B : Module.Basis (Fin (Nsec (m i))) K
            Γ((m i • cartierPullback f J).sheaf, ⊤)),
          ∀ p ∈ relWeightProfiles cX fX dd D₀ (m i • cartierPullback f J) f y B,
          (∀ (B' : Module.Basis (Fin (Nsec (m i))) K Γ((m i • cartierPullback f J).sheaf, ⊤)),
            ∀ p' ∈ relWeightProfiles cX fX dd D₀ (m i • cartierPullback f J) f y B',
              (∑ i', Real.exp (p.1 / t - p.2 i' / (m i : ℝ))) ≤
                ∑ i', Real.exp (p'.1 / t - p'.2 i' / (m i : ℝ))) →
          a ≤ p.1) →
        ∀ᶠ i in atTop, ∀ (B : Module.Basis (Fin (Nsec (m i))) K
            Γ((m i • cartierPullback f J).sheaf, ⊤)),
          ∀ p ∈ relWeightProfiles cX fX dd D₀ (m i • cartierPullback f J) f y B,
          (∀ (B' : Module.Basis (Fin (Nsec (m i))) K Γ((m i • cartierPullback f J).sheaf, ⊤)),
            ∀ p' ∈ relWeightProfiles cX fX dd D₀ (m i • cartierPullback f J) f y B',
              (∑ i', Real.exp (p.1 / t - p.2 i' / (m i : ℝ))) ≤
                ∑ i', Real.exp (p'.1 / t - p'.2 i' / (m i : ℝ))) →
          RelWeightProfileHasFibreCentre cX fX dd D₀ (m i • cartierPullback f J) f y B p := by
  obtain ⟨t, ht₀', ht, htb, l, hl, hlim⟩ :=
    exists_parameter_point_centers_le k hk ha hb (lam := (s : ℝ)) hsb ht₀
  refine ⟨t, ht₀', ht, htb, fun {ν c} hν hN hc hliminf hbdd m hm hfm h6ev hAev => ?_⟩
  -- the limit excludes the inequalities of one degree for every dimension up to n
  have hev := hlim n Nsec hν hN
    (fun j : ℕ => relWeightInfimum cX fX dd D₀ (j • cartierPullback f J) f y (Nsec j) t j /
      Nsec j)
    hc hliminf hbdd m hm hfm (fun D : ℕ => (s : ℝ) * ((s : ℝ) ^ D - 1) + (s : ℝ) * (D : ℕ))
    (fun _ => 0)
    (fun i D => ∃ (Q : ℕ → ℝ) (T A : ℝ), CenterDegreeInequalities Nsec
      (fun j : ℕ => relWeightInfimum cX fX dd D₀ (j • cartierPullback f J) f y (Nsec j) t j /
        Nsec j)
      t s ((s : ℝ) * ((s : ℝ) ^ D - 1) + (s : ℝ) * (D : ℕ)) a l (m i) D Q T A)
    (fun _ _ _ _ hP _ => hP)
  -- eventually the sections of m_i f*J are nonzero
  have hNpos : ∀ᶠ i in atTop, 0 < Nsec (m i) := by
    have h1 : ∀ᶠ j : ℕ in atTop, ν / 2 < (Nsec j : ℝ) / (j : ℝ) ^ k :=
      hN.eventually (lt_mem_nhds (half_lt_self hν))
    have h2 : ∀ᶠ j : ℕ in atTop, 0 < Nsec j := by
      refine h1.mono fun j hj => Nat.pos_of_ne_zero fun h0 => ?_
      have h0' : (Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤) : ℝ) = 0 := by
        exact_mod_cast h0
      change ν / 2 < (Module.finrank K Γ((j • cartierPullback f J).sheaf, ⊤) : ℝ) /
        (j : ℝ) ^ k at hj
      rw [h0', zero_div] at hj
      linarith
    exact hm.eventually h2
  -- eventually the degrees exceed the thresholds of all dimensions
  have hMev : ∀ᶠ i in atTop, l * (2 * s ^ k + 2 ^ k * k.factorial + n + s ^ n) ≤ m i :=
    hm.eventually (eventually_ge_atTop _)
  filter_upwards [hev, hNpos, hMev, h6ev, hAev] with i hi hNi hMi h6i hAi
  intro B p hp hpmin hBs T _ _ _ _ π _ _ _ hπ cT r ξ _ hinj hξ hsnc hBsupp hGsupp _ _ _ _ pt hpt
    hpoly
  by_contra hptF
  -- the datum of a minimizing profile has positive log discrepancy
  have hap : a ≤ p.1 := hAi B p hp hpmin
  have hp1 : 0 < p.1 := lt_of_lt_of_le ha hap
  -- the members of the model have positive log discrepancy
  have hApos : ∀ j, 0 < ((dd : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ j)) / dd := by
    intro j
    have h1 := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cX fX dd D₀ hklt cT
      ⟨ξ j, hξ j⟩
    have h2 : ((cartierCoefficient
        (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ j) : ℤ) : ℝ) <
        (dd : ℝ) := by exact_mod_cast h1
    have hdd' : (0 : ℝ) < dd := by exact_mod_cast hdd
    exact div_pos (by linarith) hdd'
  -- a weight with the same datum on the members through pt
  obtain ⟨w', hw'0, hw'ne, hw'supp, hw'A, hw'v⟩ := exists_weight_of_inSNCProfilePolytope ξ dd
    (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover)
    (fun i' => cartierPullback π (cartierSectionZeroDivisor
      (m i • cartierPullback f J) (B i') (hBs i'))) p hp1 pt hApos hpoly
  -- the generic point of its stratum and the chart data for the map to the base
  obtain ⟨η, hη, hηpt, hmax, hall⟩ := projectiveHyperplane_exists_closedPoint_tangent_chart_dense
    (π ≫ f) e he ξ hsnc w' pt hw'supp
  obtain ⟨q, hqpt, hqF⟩ := hpt
  have hqy : f (π q) = y := hqF
  have hptq : pt ⤳ q := specializes_iff_mem_closure.mpr hqpt
  have hηq : η ⤳ q := hηpt.trans hptq
  have hηy : (π ≫ f) η ⤳ y := by
    rw [← hqy]
    exact (π ≫ f).base.hom.map_specializes hηq
  have hηne : (π ≫ f) η ≠ y := by
    intro heq
    apply hptF
    have h1 : (π ≫ f) η ⤳ (π ≫ f) pt := (π ≫ f).base.hom.map_specializes hηpt
    rw [heq] at h1
    have h2 : (π ≫ f) pt ∈ ({y} : Set Y) := by
      rw [← hyc.closure_eq]
      exact specializes_iff_mem_closure.mp h1
    exact h2
  -- a coordinate chart of projective space containing the image of η
  obtain ⟨i₀, hi₀⟩ := polynomialProjective_exists_coordinate_chart N K (e ((π ≫ f) η))
  have hηk : (π ≫ f) η ∈ projectivePullbackCoordinateOpen e i₀ := hi₀
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : {k : Fin N // Nonempty (projectivePullbackCoordinateOpen e k)},
      k₀.val = i₀ := ⟨⟨i₀, ⟨⟨(π ≫ f) η, hηk⟩⟩⟩, rfl⟩
  have hηk₀ : (π ≫ f) η ∈ projectivePullbackCoordinateOpen e k₀.val := by
    rw [hk₀]
    exact hηk
  -- the closed points of the specialization comparison, and a closed point over them
  obtain ⟨G, hGdense, hG6⟩ := h6i ((π ≫ f) η) hηy hηne
  have hsmT : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨z, hzcl, hηz, -, hzG, hzU, c, σc, hz, hηc, Tan, ez, hc, hez, hiff, hTanfree, hTanU,
    hsat, hTanne⟩ := hall k₀ hηk₀ Set.univ isOpen_univ (Set.mem_univ η) ((π ≫ f) ⁻¹' G)
      fun O hO hηO => by
        obtain ⟨z', hzO, hzc, hzη, hzG'⟩ := hGdense T (π ≫ f) η rfl O hO hηO
        exact ⟨z', hzG', hzc, hzη, hzO⟩
  -- the image of z is a closed point different from the image of η
  have hπzcl : IsClosed ({(π ≫ f) z} : Set Y) := by
    have h1 := (hfcl.comp π.isClosedMap) _ hzcl
    rwa [Set.image_singleton] at h1
  have hηz' : (π ≫ f) η ⤳ (π ≫ f) z := (π ≫ f).base.hom.map_specializes hηz
  have hneπ : (π ≫ f) η ≠ (π ≫ f) z := by
    intro heq
    apply hηne
    have h1 : y ∈ closure ({(π ≫ f) η} : Set Y) := specializes_iff_mem_closure.mp hηy
    rw [heq, hπzcl.closure_eq] at h1
    rw [heq]
    exact (Set.mem_singleton_iff.mp h1).symm
  obtain ⟨d, hTan⟩ : ∃ d, Tan.card = d + 1 :=
    ⟨Tan.card - 1, by have := Finset.card_pos.mpr (hTanne hneπ); omega⟩
  have hdn : d + 1 ≤ n := by
    have h1 := Finset.card_le_univ Tan
    rw [Fintype.card_fin, hTan] at h1
    exact h1
  -- the dimension and the degree of the image of the centre
  obtain ⟨D', hD'k, hD'⟩ := hdim ((π ≫ f) η) hηy
  have hgW : g ∉ ((pointClosureι ((π ≫ f) η) ≫ e)
      (genericPoint (pointClosureScheme ((π ≫ f) η)))).asHomogeneousIdeal := by
    rw [Scheme.Hom.comp_apply, pointClosureι_genericPoint]
    exact (Proj.mem_basicOpen _ _ _).mp ((e.base.hom.map_specializes hηy).mem_open
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin N) K) g).isOpen
      ((Proj.mem_basicOpen _ _ _).mpr hgy))
  -- the thresholds
  have hM : l * (2 * s ^ D' + 2 ^ D' * D'.factorial + (d + 1) + s ^ (d + 1)) ≤ m i := by
    refine le_trans (Nat.mul_le_mul_left l ?_) hMi
    have h1 : s ^ D' ≤ s ^ k := Nat.pow_le_pow_right hs hD'k
    have h2 : 2 ^ D' * D'.factorial ≤ 2 ^ k * k.factorial :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hD'k) (Nat.factorial_le hD'k)
    have h3 : s ^ (d + 1) ≤ s ^ n := Nat.pow_le_pow_right hs hdn
    omega
  -- the objective of the new weight is the objective of the datum
  have hobj : (∑ i', Real.exp ((∑ k', w' k' * (((dd : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cX fX dd D₀ cT etaleCharts_cover) (ξ k')) / dd)) / t -
      (∑ k', w' k' * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
        (m i • cartierPullback f J) (B i') (B.ne_zero i'))) (ξ k') : ℝ)) /
          (m i : ℝ))) = ∑ i', Real.exp (p.1 / t - p.2 i' / (m i : ℝ)) := by
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← hw'A, ← hw'v i']
  have hmin : (∑ i', Real.exp (p.1 / t - p.2 i' / (m i : ℝ))) ≤
      relWeightInfimum cX fX dd D₀ (m i • cartierPullback f J) f y (Nsec (m i)) t (m i) :=
    le_relWeightInfimum _ _ _ _ _ _ _ _ _ _ ⟨_, B, p, hp, rfl⟩ fun B' p' hp' => hpmin B' p' hp'
  -- (6) over the base at the image of z, and the infimum at π z
  have hspec := hG6 ((π ≫ f) z) hπzcl hzG hηz'
  have hneπz : (sncWeightObjectiveValues cX fX dd D₀ (m i • cartierPullback f J) (π z)
      (Nsec (m i)) t (m i)).Nonempty :=
    ⟨_, sncWeightObjectiveValues_natCast_mem cX fX dd D₀ _ (π z) B t (m i)⟩
  have hπz := relWeightInfimum_le_sncWeightInfimum cX fX dd D₀ (m i • cartierPullback f J) f
    (x := π z) (y := (π ≫ f) z) rfl (Nsec (m i)) t (m i) hneπz
  have hineq := rel_projectiveHyperplane_centerDegreeInequalities π hπ f e g hg hggen he happ k₀
    cX fX hdd D₀ cT ξ hinj hξ hsnc hBsupp c σc hc w' hw'0 hw'ne η hηc hη hmax y q hηq hqy z hz
    hηz hzU ez hez hiff Tan hTan hTanfree hTanU hsat MonomialOrder.lex s hs hD' hgW
    (hdeg ((π ≫ f) η) hgW D' hηy hηne hD') l (m i) (by omega) hM B hGsupp hNi ht a
    (by rw [← hw'A]; exact hap) (by rw [hobj]; exact hmin)
    (by rw [hobj]; exact (hmin.trans hspec).trans hπz)
  exact hi (d + 1) (Nat.succ_pos d) hdn ⟨_, _, _, hineq⟩

end FibreCentre

end MixedFujita
