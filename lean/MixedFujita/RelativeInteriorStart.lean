/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeFibreCharts
public import MixedFujita.RelativeFibreTestPrime
public import MixedFujita.RelativeWeightProfiles
public import MixedFujita.KltBoundaryFreeNumericalStart
public import MixedFujita.GenericSmoothCharts
public import MixedFujita.SameDimensionSteinBirational
public import MixedFujita.SteinCartierSectionEquiv
public import MixedFujita.ResolutionChartOfPrime
public import MixedFujita.BirationalAmbroDescent
public import MixedFujita.KltMinimizerDataShift

/-!
The interior gap of section 7 relative to f (step 17R-2).

Let (X, B) be a projective klt pair of dimension n = m + k, f : X → Y a contraction onto a
projective variety of dimension k and A an ample divisor of Y with c j^k ≤ h⁰(j A) and
k / b < k/(k+1) (k! c)^{1/k}. The sections of j A on Y are the sections of f*(j A) on X
(`steinCartierSectionEquiv`). At every closed point y of Y, for t in a fixed interval [t₀, b] and
all large j, the infimum over the fibre of y of the objective of the profile data of the sections
of f*(j A) is at most h⁰(j A)(1 − δ) (`rel_klt_ample_interior_of_dimension_lower_and_closedPoints`),
when the rational realization loci of the pair on X are closed on closed points.

The proof is that of section 7 with the ordinary point x replaced by a general point of X and its
fibre:

* the base has an étale chart of dimension k (generic smoothness) and a nonempty open W of X
  consists of boundary-free points of the reference chart at which, for every K-point of the base,
  there is a fibre chart (`exists_open_fibreCharts`, from `exists_generic_fibreCharts_on_chart`);
* a very general closed point x of W transfers every rational profile realized over the fibre of
  f(x) to the fibre of y in all large degrees (`exists_closedPoint_rel_all_degree_transfer`): the
  realization loci over the base are closed on closed points and their preimages are proper
  closed subsets of X;
* at x the fibre test prime has log discrepancy k, so the Taylor start (7) at f(x) on Y with k
  variables, transported to X by the Stein identification, bounds the infimum over the fibre of
  f(x); Lemma 1 on X bounds the vanishing orders at f(x).
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

section Charts

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

omit [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] in
/-- An integral scheme of finite type and dimension k over a perfect field has an étale chart with
k coordinates (at a point of the smooth locus). -/
theorem exists_etaleChart_of_topologicalKrullDim [PerfectField K] {k : ℕ}
    (hdim : topologicalKrullDim Y = k) : Nonempty (EtaleChart K Y k) := by
  obtain ⟨y, -, -, hys⟩ := exists_closedPoint_mem_open_smoothLocus (K := K) (Set.univ : Set Y)
    isOpen_univ Set.univ_nonempty
  obtain ⟨m', c, -⟩ := exists_etaleChart_of_mem_smoothLocus (K := K) hys
  have h := etaleChart_topologicalKrullDim c
  rw [hdim] at h
  have hm : m' = k := by exact_mod_cast h.symm
  subst hm
  exact ⟨c⟩

/-- A nonempty open set of fibre charts: boundary-free points of the reference chart over the
chart of the base at which, for every K-point of the base, some étale chart of X has as last
coordinates the pullbacks of the base coordinates centred at the image point. -/
theorem exists_open_fibreCharts [CharZero K] {m k : ℕ} (f : X ⟶ Y) [IsDominant f]
    [f.IsOver (Spec (CommRingCat.of K))] (cX : EtaleChart K X (m + k)) (fX : X.functionFieldˣ)
    (d : ℕ) (D₀ : CartierDivisor X) (cY : EtaleChart K Y k) :
    ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ x ∈ W, ∃ (_ : x ∈ cX.U) (hy : f x ∈ cY.U),
      D₀.IsLocalEquationAt x (fX ^ d) ∧ ∀ β : Y.presheaf.stalk (f x) →ₐ[K] K,
        ∃ (Fc : EtaleChart K X (m + k)) (hx : x ∈ Fc.U),
          ∀ l : Fin k, etaleChartStalkCoords Fc x hx (MvPolynomial.X (Fin.natAdd m l)) =
            f.stalkMap x (Y.presheaf.germ cY.U (f x) hy
              ((etaleChartCentered cY (rationalAffineGermPoint (f x) hy β)).coords
                (MvPolynomial.X l))) := by
  classical
  obtain ⟨V, hVU, hVne, -, hVD⟩ := exists_dense_open_localEquation D₀ (fX ^ d) cX.U cX.nonempty
  have : Nonempty cY.U := cY.nonempty
  have hpre : Nonempty (f ⁻¹ᵁ cY.U) := dominant_preimage_nonempty f cY.U
  obtain ⟨x₀, hx₀V, hx₀Y⟩ : ((V : Set X) ∩ f ⁻¹ᵁ cY.U).Nonempty := by
    obtain ⟨⟨a, ha⟩⟩ := hVne
    obtain ⟨⟨b, hb⟩⟩ := hpre
    exact nonempty_preirreducible_inter V.isOpen (f ⁻¹ᵁ cY.U).isOpen ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨g, hgle, hx₀g⟩ := cX.isAffine.exists_basicOpen_le (V := V ⊓ f ⁻¹ᵁ cY.U)
    ⟨x₀, hx₀V, hx₀Y⟩ (hVU hx₀V)
  let c₁ := etaleChartBasicOpen cX g ⟨⟨x₀, hx₀g⟩⟩
  have hc₁le : c₁.U ≤ f ⁻¹ᵁ cY.U := fun z hz => (hgle hz).2
  have hc₁V : c₁.U ≤ V := fun z hz => (hgle hz).1
  have hc₁X : c₁.U ≤ cX.U := X.basicOpen_le g
  -- the base ring and the map of sections
  have : Algebra.FiniteType K Γ(Y, cY.U) := sectionsBaseOpen_finiteType cY.isAffine
  let φ : Γ(Y, cY.U) →ₐ[K] Γ(X, c₁.U) := appLEAlgHom f cY.U c₁.U hc₁le
  have hgerm : ∀ (z : X) (hz : z ∈ c₁.U) (s : Γ(Y, cY.U)),
      X.presheaf.germ c₁.U z hz (φ s) = f.stalkMap z (Y.presheaf.germ cY.U (f z) (hc₁le hz) s) := by
    intro z hz s
    rw [Scheme.Hom.germ_stalkMap_apply]
    simp only [φ, appLEAlgHom, AlgHom.coe_mk, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  obtain ⟨h, hh0, hgen⟩ := exists_generic_fibreCharts_on_chart (n := m) (d := k) (r := 0) c₁
    Fin.elim0 Fin.elim0 ⟨fun i => i.elim0, fun i => i.elim0⟩ Γ(Y, cY.U) φ
  -- the open set: the chart over the basic open of h
  have hbo : (Y.basicOpen h : Set Y).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    apply hh0
    rw [← basicOpen_eq_bot_iff]
    exact Opens.ext he
  have : Nonempty (Y.basicOpen h) := hbo.to_subtype
  have hpre₂ : Nonempty (f ⁻¹ᵁ Y.basicOpen h) := dominant_preimage_nonempty f (Y.basicOpen h)
  refine ⟨c₁.U ⊓ f ⁻¹ᵁ Y.basicOpen h, ?_, ?_⟩
  · obtain ⟨⟨a, ha⟩⟩ := hpre₂
    exact nonempty_preirreducible_inter c₁.U.isOpen (f ⁻¹ᵁ Y.basicOpen h).isOpen
      ⟨x₀, hx₀g⟩ ⟨a, ha⟩
  · rintro x ⟨hxc₁, hxh⟩
    have hy : f x ∈ cY.U := hc₁le hxc₁
    refine ⟨hc₁X hxc₁, hy, hVD x (hc₁V hxc₁), fun β => ?_⟩
    have hunit : IsUnit (X.presheaf.germ c₁.U x hxc₁ (φ h)) := by
      rw [hgerm]
      exact ((Y.mem_basicOpen h (f x) hy).mp hxh).map (f.stalkMap x).hom
    set cYc := etaleChartCentered cY (rationalAffineGermPoint (f x) hy β) with hcYc
    have hb1 : IsUnit (X.presheaf.germ c₁.U x hxc₁ (φ 1)) := by
      rw [map_one, map_one]
      exact isUnit_one
    have hloc : (algebraMap Γ(Y, cY.U) (Localization.Away (1 : Γ(Y, cY.U)))).FormallyEtale :=
      RingHom.formallyEtale_algebraMap.mpr
        (Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (1 : Γ(Y, cY.U))))
    have hu : (MvPolynomial.aeval (R := K) (fun l => algebraMap Γ(Y, cY.U)
        (Localization.Away (1 : Γ(Y, cY.U))) (cYc.coords (MvPolynomial.X l)))).toRingHom.FormallyEtale := by
      have heq : (MvPolynomial.aeval (R := K) (fun l => algebraMap Γ(Y, cY.U)
          (Localization.Away (1 : Γ(Y, cY.U))) (cYc.coords (MvPolynomial.X l)))) =
          (IsScalarTower.toAlgHom K Γ(Y, cY.U) (Localization.Away (1 : Γ(Y, cY.U)))).comp
            cYc.coords := by
        apply MvPolynomial.algHom_ext
        intro l
        rw [MvPolynomial.aeval_X]
        rfl
      rw [heq]
      exact RingHom.FormallyEtale.comp cYc.formallyEtale hloc
    obtain ⟨Fc, hFc, -, -, -, -, hcoord⟩ := hgen x hxc₁ hunit
      (fun l => cYc.coords (MvPolynomial.X l)) 1 hb1 hu
    exact ⟨Fc, hFc, fun l => (hcoord l).trans (hgerm x hxc₁ _)⟩

end Charts

section Transfer

variable {K : Type u} [Field K] [IsAlgClosed K] [Uncountable K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- A very general closed point of a nonempty open set of X transfers, in all large degrees,
every rational normalized profile realized over the fibre of its image to the fibre of a given
closed point y of the base, when the rational realization loci on X are closed on closed points
and f is a dominant closed map. -/
theorem exists_closedPoint_rel_all_degree_transfer [CompactSpace X] (cX : EtaleChart K X n)
    (fX : X.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor X) (f : X ⟶ Y) [IsDominant f]
    (hf : IsClosedMap f) (G : ℕ → CartierDivisor X)
    (hcl : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((G j).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {x : X | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cX fX d D₀ (G j) (Module.finrank K Γ((G j).sheaf, ⊤)) x})
    (y : Y) (hyc : IsClosed ({y} : Set Y)) (O : Set X) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ x : X, IsClosed ({x} : Set X) ∧ x ∈ O ∧ ∀ᶠ j : ℕ in atTop,
      ∀ α : Fin (Module.finrank K Γ((G j).sheaf, ⊤)) → ℚ,
        (fun i => (α i : ℝ)) ∈ relWeightNormalizedProfiles cX fX d D₀ (G j) f
          (Module.finrank K Γ((G j).sheaf, ⊤)) (f x) →
        (fun i => (α i : ℝ)) ∈ relWeightNormalizedProfiles cX fX d D₀ (G j) f
          (Module.finrank K Γ((G j).sheaf, ⊤)) y := by
  classical
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hcl
  let I := {a : (Σ j : ℕ, Fin (Module.finrank K Γ((G j).sheaf, ⊤)) → ℚ) // J ≤ a.1}
  have hrel : ∀ a : I, IsClosedOnClosedPoints {y' : Y | (fun i => (a.1.2 i : ℝ)) ∈
      relWeightNormalizedProfiles cX fX d D₀ (G a.1.1) f
        (Module.finrank K Γ((G a.1.1).sheaf, ⊤)) y'} := fun a =>
    relWeightNormalizedProfiles_isClosedOnClosedPoints cX fX d D₀ (G a.1.1) f hf _ a.1.2
      (hJ a.1.1 a.2 a.1.2)
  choose Z hZ hrep using hrel
  obtain ⟨x, hxc, hxO, hxbad⟩ := exists_closedPoint_mem_open_notMem_of_countable (K := K) O hO hOne
    (fun a : {a : I // Z a ≠ Set.univ} => f ⁻¹' Z a.1)
    (fun a => (hZ a.1).preimage f.continuous)
    (fun a h => a.2 (by
      have hsub : Set.range f ⊆ Z a.1 := by
        rintro _ ⟨z, rfl⟩
        have hz : z ∈ f ⁻¹' Z a.1 := h ▸ Set.mem_univ z
        exact hz
      have h1 : closure (Set.range f) ⊆ Z a.1 := (hZ a.1).closure_subset_iff.mpr hsub
      rw [f.denseRange.closure_range] at h1
      exact Set.univ_subset_iff.mp h1))
  refine ⟨x, hxc, hxO, ?_⟩
  filter_upwards [eventually_ge_atTop J] with j hj
  intro α hα
  let a : I := ⟨⟨j, α⟩, hj⟩
  have hfxc : IsClosed ({f x} : Set Y) := by simpa using hf _ hxc
  have hxZ : f x ∈ Z a := (hrep a (f x) hfxc).mp hα
  have hEq : Z a = Set.univ := by
    by_contra hne
    exact hxbad ⟨a, hne⟩ hxZ
  exact (hrep a y hyc).mpr (hEq ▸ Set.mem_univ y)

end Transfer

section Interior

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- The interior gap of section 7 relative to f: at every closed point y of the base, for t in a
fixed interval and all large j, the infimum over the fibre of y of the objective of the profile
data of the sections of f*(j A) is at most h⁰(j A)(1 − δ). -/
theorem rel_klt_ample_interior_of_dimension_lower_and_closedPoints {n k : ℕ} (hk : 1 ≤ k)
    (hdimX : topologicalKrullDim X = n) (hdimY : topologicalKrullDim Y = k)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ : CartierDivisor X) (hklt : LogPairIsKlt cX fX d D₀) {H : CartierDivisor X}
    (hH : CartierIsAmpleProj K H) (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
    (A : CartierDivisor Y) (hA : CartierIsAmpleProj K A) {c b : ℝ} (hc : 0 < c) (hb : 0 < b)
    (hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ k ≤ (Module.finrank K Γ((j • A).sheaf, ⊤) : ℝ))
    (hvol : (k : ℝ) / b < (k : ℝ) / (k + 1) * ((k.factorial : ℝ) * c) ^ (k : ℝ)⁻¹)
    (hcl : ∀ᶠ j : ℕ in atTop,
      ∀ α : Fin (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {x : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cX fX d
          D₀ (cartierPullback f (j • A))
          (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤)) x})
    (y : Y) (hyc : IsClosed ({y} : Set Y)) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ δ > 0, ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤) ∧
      ∀ t, t₀ ≤ t → t ≤ b →
        relWeightInfimum cX fX d D₀ (cartierPullback f (j • A)) f y
          (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤)) t j ≤
          (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤) : ℝ) * (1 - δ) := by
  classical
  -- the dimensions: n = m + k
  have hkn : k ≤ n := by
    have h := dominant_topologicalKrullDim_le (K := K) f
    rw [hdimX, hdimY] at h
    exact_mod_cast h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, by omega⟩
  -- properness
  have := cartierIsAmpleProj_isProper_base H hH
  have := cartierIsAmpleProj_isProper_base A hA
  have : IsProper (f ≫ (Y ↘ Spec (CommRingCat.of K))) := by
    rw [HomIsOver.comp_over]
    infer_instance
  have : IsProper f := IsProper.of_comp f (Y ↘ Spec (CommRingCat.of K))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  have hfcl : IsClosedMap f := f.isClosedMap
  -- an étale chart of the base and the open set of fibre charts
  obtain ⟨cY⟩ := exists_etaleChart_of_topologicalKrullDim (K := K) hdimY
  obtain ⟨W, hWne, hWfib⟩ := exists_open_fibreCharts f cX fX d D₀ cY
  -- Lemma 1 on X for the pullback of A
  obtain ⟨C, -, hC⟩ := rel_vanishingOrder_le_of_fibre_point hk f cX fX d hd D₀
    (cartierPullback f A) hklt hH
  -- a very general closed point of the open set
  obtain ⟨x, hxc, hxW, htransfer⟩ := exists_closedPoint_rel_all_degree_transfer cX fX d D₀ f hfcl
    (fun j => cartierPullback f (j • A)) hcl y hyc W W.isOpen hWne
  obtain ⟨hxX, hy, hD, hfibβ⟩ := hWfib x hxW
  have hfxc : IsClosed ({f x} : Set Y) := by simpa using hfcl _ hxc
  obtain ⟨β⟩ := affineOpen_closedPoint_has_localEvaluation (K := K) cY.isAffine (f x) hy hfxc
  obtain ⟨Fc, hFc, hfib⟩ := hfibβ β
  -- the Taylor expansion at f x
  obtain ⟨coords, -, -⟩ := etaleChart_exists_taylorCoordinates cY (f x) hy β
  obtain ⟨g, hg⟩ := A.exists_isLocalEquationAt (f x)
  let T := cartierGradedTaylor A (f x) g hg coords
  have hTinj : ∀ j, Function.Injective (T j) :=
    fun j => cartierGradedTaylor_injective A (f x) g hg coords j
  have heq : ∀ j s, (T j s).order = cartierSectionVanishingOrder (j • A) (f x) s := by
    intro j s
    exact cartierTaylorCoordinates_order_eq_vanishingOrder (j • A) (f x) (g ^ j)
      (cartierLocalEquation_pow A (f x) g hg j) coords s
  -- the Stein identification of the sections
  let e : ∀ j : ℕ, Γ((j • A).sheaf, ⊤) ≃ₗ[K] Γ((cartierPullback f (j • A)).sheaf, ⊤) :=
    fun j => steinCartierSectionEquiv f K happ (j • A)
  have hfinY : ∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤) :=
    cartierIsAmpleProj_finiteDimensional_nsmul hdimY hk hA
  have hfinX : ∀ j : ℕ, FiniteDimensional K Γ((cartierPullback f (j • A)).sheaf, ⊤) :=
    fun j => LinearEquiv.finiteDimensional (e j)
  have hrank : ∀ j : ℕ, Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤) =
      Module.finrank K Γ((j • A).sheaf, ⊤) := fun j => (e j).finrank_eq.symm
  let T' : ∀ j : ℕ, Γ((cartierPullback f (j • A)).sheaf, ⊤) →ₗ[K] MvPowerSeries (Fin k) K :=
    fun j => (T j).comp (e j).symm.toLinearMap
  have hT'inj : ∀ j, Function.Injective (T' j) := fun j => (hTinj j).comp (e j).symm.injective
  -- the zero divisors of the sections on X are the pullbacks of those on Y
  have hZ : ∀ (j : ℕ) (s : Γ((cartierPullback f (j • A)).sheaf, ⊤)) (hs : s ≠ 0)
      (hs' : (e j).symm s ≠ 0),
      cartierSectionZeroDivisor (cartierPullback f (j • A)) s hs =
        cartierPullback f (cartierSectionZeroDivisor (j • A) ((e j).symm s) hs') := by
    intro j s hs hs'
    have h1 : s = cartierDominantPullbackSection f (j • A) ((e j).symm s) :=
      ((e j).apply_symm_apply s).symm
    rw [cartierSectionZeroDivisor_eq_of_eq h1 hs
      (cartierDominantPullbackSection_ne_zero f (j • A) _ hs'),
      cartierDominantPullbackSection_zeroDivisor]
  -- Lemma 1 bounds the orders of the Taylor expansions
  have hord : ∀ᶠ j : ℕ in atTop, ∀ s : Γ((cartierPullback f (j • A)).sheaf, ⊤), s ≠ 0 →
      realWeightedOrder (fun _ : Fin k => (1 : ℝ)) (T' j s) ≤ ((C : ℝ) * k) * j := by
    filter_upwards [eventually_ge_atTop 1] with j hj s hs
    have hs' : (e j).symm s ≠ 0 := (LinearEquiv.map_ne_zero_iff _).mpr hs
    have hT0 : T' j s ≠ 0 := fun h => hs (hT'inj j (h.trans (map_zero _).symm))
    have hnat := realWeightedOrder_natCast (fun _ : Fin k => 1) hT0
    simp only [Nat.cast_one] at hnat
    rw [hnat]
    change ((T j ((e j).symm s)).order.toNat : ℝ) ≤ _
    rw [heq]
    have hCj := hC x hxX hD Fc hFc cY hy β hfib j hj (j • A) ((e j).symm s) hs'
    rw [← cartierPullback_nsmul] at hCj
    calc ((cartierSectionVanishingOrder (j • A) (f x) ((e j).symm s)).toNat : ℝ)
        ≤ (C : ℝ) * j * k := hCj s hs (hZ j s hs hs')
      _ = ((C : ℝ) * k) * j := by ring
  -- the growth of the sections on X
  have hN' : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ k ≤
      (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤) : ℝ) := by
    filter_upwards [hN] with j hj
    rw [hrank]
    exact hj
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ := taylor_interior_start_of_dimension_lower
    (show 0 < k from hk) T' hT'inj hc hb (by positivity : (0 : ℝ) ≤ (C : ℝ) * k) hN' hord hvol
  refine ⟨t₀, ht₀, ht₀b, δ, hδ, ?_⟩
  filter_upwards [hev, htransfer, hN', eventually_ge_atTop 1] with j hj hjtr hjN hj1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hNpos : 0 < Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤) := by
    exact_mod_cast (mul_pos hc (pow_pos hj0 k)).trans_le hjN
  refine ⟨hNpos, fun t ht₀t htb => ?_⟩
  have ht : 0 < t := ht₀.trans_le ht₀t
  obtain ⟨B, hB⟩ := hj t ht₀t htb
  -- the profile datum at x of the basis, from the fibre test prime
  have hs' : ∀ i, (e j).symm (B i) ≠ 0 := fun i =>
    (LinearEquiv.map_ne_zero_iff _).mpr (B.ne_zero i)
  obtain ⟨p, hp, hple⟩ := rel_exists_sncWeightProfile_le_of_fibre_point hk f cX fX d hd D₀
    (cartierPullback f (j • A)) (j • A) B B.ne_zero (fun i => (e j).symm (B i)) hs'
    (fun i => hZ j (B i) (B.ne_zero i) (hs' i)) x hxX hD Fc hFc cY hy β hfib ht hj0 hζ.le
  have hvals : (fun i => ζ * realWeightedOrder (fun _ : Fin k => (1 : ℝ)) (T' j (B i))) =
      (fun i => ζ * ((cartierSectionVanishingOrder (j • A) (f x)
        ((e j).symm (B i))).toNat : ℝ)) := by
    funext i
    have hT0 : T' j (B i) ≠ 0 := fun h => B.ne_zero i (hT'inj j (h.trans (map_zero _).symm))
    have hnat := realWeightedOrder_natCast (fun _ : Fin k => 1) hT0
    simp only [Nat.cast_one] at hnat
    rw [hnat]
    change ζ * ((T j ((e j).symm (B i))).order.toNat : ℝ) = _
    rw [heq]
  rw [hvals] at hB
  have h5 : (∑ i, Real.exp (ζ * k / t - ζ * ((cartierSectionVanishingOrder (j • A) (f x)
      ((e j).symm (B i))).toNat : ℝ) / j)) =
      (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤) : ℝ) *
        minimizationFunctional j t (ζ * k) (fun i => ζ * ((cartierSectionVanishingOrder (j • A)
          (f x) ((e j).symm (B i))).toNat : ℝ)) :=
    sum_exp_eq_mul_minimizationFunctional hNpos j t _ _
  have hfx : relWeightInfimum cX fX d D₀ (cartierPullback f (j • A)) f (f x)
      (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤)) t j ≤
      (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤) : ℝ) * (1 - δ) :=
    (relWeightInfimum_le cX fX d D₀ (cartierPullback f (j • A)) f (f x) t j B
      ⟨x, rfl, hp⟩).trans (hple.trans (h5.trans_le
        (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _))))
  have hne : (relWeightObjectiveValues cX fX d D₀ (cartierPullback f (j • A)) f (f x)
      (Module.finrank K Γ((cartierPullback f (j • A)).sheaf, ⊤)) t j).Nonempty :=
    ⟨_, B, p, ⟨x, rfl, hp⟩, rfl⟩
  exact (relWeightInfimum_le_of_rational cX fX hd D₀ _ hklt f hNpos hj1 t hjtr hne).trans hfx

end Interior

end MixedFujita
