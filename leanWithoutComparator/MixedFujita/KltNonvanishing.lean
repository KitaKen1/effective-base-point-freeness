/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltUniquePlaceNonvanishing
public import MixedFujita.KltUniquePlaceRoundupModel
public import MixedFujita.KltStableBaseLocusCenter
public import MixedFujita.BirationalSNCBasePointRemoval
public import MixedFujita.ReducedInvertibleSectionGeneration
public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.KltBasePointFreeIitaka
public import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedRegWindow

public import MixedFujita.OriginalBPFIsolatedRestrictedZeroCenter

/-! Nonvanishing from the original klt adjoint hypotheses, without an Iitaka input. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Topology
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

attribute [local instance] Classical.propDecidable

/-- Nonvanishing lifted from an isolated numerically trivial lc centre. -/
theorem klt_isolated_numericallyTrivial_center_eventually_nonzero_section
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 2 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D) (a : ℕ)
    (hnefa : CartierIsNef K ((r * a) • D - D'))
    (d₃ : ℕ) (hd₃ : 1 ≤ d₃) (D₃ : CartierDivisor X)
    (heff₃ : LogPairBoundaryEffective c₀ f₀ d₃ D₃)
    (hlc₃ : LogPairIsLogCanonical c₀ f₀ d₃ D₃) (η : X)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c₀ f₀ d₃ D₃) ↔ x ∈ closure {η})
    (b₃ : ℕ) (hamp₃ : ∀ j : ℕ, b₃ ≤ j → CartierIsAmpleProj K ((d₃ * j) • D - D₃))
    (hdeg : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
      [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim C = 1 → ∀ (φ : C ⟶ X) [φ.IsOver (Spec (CommRingCat.of K))],
      Set.range φ ⊆ closure {η} → cartierCurvePullbackDegree (K := K) D φ = 0) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ s : Γ((m • D).sheaf, ⊤), s ≠ 0 := by
  -- the unique lc place over it
  obtain ⟨T, hTi, hTo, hTN, hTs, hTp, p, hpdom, hpover, hpprop, hp, cT, R, ξ, i₀, B, E, S, hE, hS,
    dT, b₀, hinj, hξ, hsnc, hJT, hexc, hE₀, hSI, -, hdT, hBsupp, hround, hB₀, hpξ, hampT⟩ :=
    klt_isolated_center_exists_unique_place_roundup_model K hdim (by omega) hnorm hcov J hJ c₀ f₀
      r hr D' heff hklt d₃ hd₃ D₃ heff₃ hlc₃ η hNK D hD a hnefa b₃ hamp₃
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hTp
  let := hpdom
  let := hpover
  let := hpprop
  have hdimT : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  -- the pullback of D and its ample adjoints
  have hampP : ∀ m : ℕ, b₀ ≤ m →
      CartierIsAmpleProj K (dT • (m • cartierPullback p D - smoothCanonicalDivisor cT) - B) := by
    intro m hm
    have h := hampT m hm
    rwa [cartierPullback_nsmul] at h
  -- the place maps into the centre
  have hpS : ∀ y ∈ closure ({ξ i₀} : Set T), p y ∈ closure ({η} : Set X) := by
    intro y hy
    have h1 : p '' closure ({ξ i₀} : Set T) ⊆ closure (p '' {ξ i₀}) :=
      image_closure_subset_closure_image p.continuous
    have h2 : closure (p '' ({ξ i₀} : Set T)) ⊆ closure ({η} : Set X) := by
      rw [Set.image_singleton]
      exact closure_minimal (Set.singleton_subset_iff.mpr hpξ) isClosed_closure
    exact h2 (h1 ⟨y, hy, rfl⟩)
  -- the pullback of D has degree zero on curves in the place
  have hPdeg : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
      [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim C = 1 → ∀ φ : C ⟶ T,
        φ ≫ (T ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K) →
        Set.range φ ⊆ closure ({ξ i₀} : Set T) →
        cartierCurvePullbackDegree (K := K) (cartierPullback p D) φ = 0 := by
    intro C _ _ _ _ hC φ hφ hrange
    rw [cartierCurvePullbackDegree_cartierPullback_of_dominant hC p φ D]
    let : (φ ≫ p).IsOver (Spec (CommRingCat.of K)) :=
      ⟨by rw [Category.assoc, HomIsOver.comp_over (f := p) (S := Spec (CommRingCat.of K)), hφ]⟩
    apply hdeg C hC (φ ≫ p)
    rintro _ ⟨c, rfl⟩
    exact hpS (φ c) (hrange ⟨c, rfl⟩)
  -- nonvanishing on the place
  obtain ⟨N₁, hN₁⟩ := klt_unique_place_eventually_restricted_section K hn cT ξ i₀ hinj hξ hsnc
    hJT (cartierPullback p D) B E S hE hS dT b₀ hE₀ hSI hdT hBsupp hround hB₀ hampP hPdeg
  refine ⟨max N₁ b₀, fun m hm => ?_⟩
  obtain ⟨t, ht⟩ : ∃ t : Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj
      (cartierPullback p (m • D) + E).sheaf, ⊤), t ≠ 0 := by
    rw [cartierPullback_nsmul]
    exact hN₁ m (le_of_max_le_left hm)
  -- the section generates somewhere on the reduced place
  let : IsReduced (effectiveCartierIdealSheaf S hS).subscheme :=
    hSI ▸ Hironaka.Resolution.isReduced_subscheme_vanishingIdeal _
  obtain ⟨z, W, hzW, a, hunit⟩ := nonzero_invertible_section_generates_somewhere_on_reduced _
    (cartierPullbackSheaf_isInvertible _ _) t ht
  -- the lifting
  have hA := hampT m (le_of_max_le_right hm)
  have hx := original_basepoint_removed_of_usual_KV_snc_roundup_cut K
    (kawamataViehwegVanishingSNC_of_charZero K n) p hp hnorm J hJ (m • D) cT ξ hinj hξ hsnc
    B E S hE hexc hS dT hdT hBsupp hround (cartierIsAmpleProj_isNef hA)
    (cartierIsAmpleProj_isBig hdimT (by omega) hA) z W hzW a t hunit
  let x := p ((effectiveCartierIdealSheaf S hS).subschemeι z)
  have hxgen : x ∈ cartierGenerationOpen (m • D) := not_not.mp hx
  obtain ⟨s, hs⟩ := (mem_cartierGenerationOpen_iff (m • D) x).mp hxgen
  exact ⟨s, (cartierSectionNonvanishingOpen_nonempty_iff (m • D) s).mp ⟨⟨x, hs⟩⟩⟩

/-- Numerical dimension zero supplies nonvanishing without a seed section. -/
theorem klt_nef_numericalZero_eventually_nonzero_section
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D) (a : ℕ)
    (hnef : CartierIsNef K ((r * a) • D - D')) (hbig : CartierIsBig K ((r * a) • D - D'))
    (hzero : cartierNumericalDimension K n hdim D J = 0) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ s : Γ((m • D).sheaf, ⊤), s ≠ 0 := by
  have hneg := proper_nef_numericalDimension_zero_neg_isNef K n hdim hn D J hD hJ hzero
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, ρ, ξ, A, E,
    hinj, hξ, hsnc, hA, hE, hexc, hEc, hpush, hvan⟩ :=
    exists_klt_resolution_higher_vanishing_model K hnorm hcov c₀ f₀ r hr D' heff hklt
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  have hvanm (m q : ℕ) :
      Subsingleton (Scheme.Modules.Cohomology (E + m • cartierPullback p D).sheaf (q + 1)) := by
    have hsplit : r • (m • D) - D' =
        ((r * a) • D - D') + ((r * m) • D + (r * a) • (-D)) := by
      rw [smul_smul, smul_neg]
      abel
    have hnefextra := cartierIsNef_add (cartierIsNef_nsmul hD (r * m))
      (cartierIsNef_nsmul hneg (r * a))
    have hnefm : CartierIsNef K (r • (m • D) - D') := by
      rw [hsplit]
      exact cartierIsNef_add hnef hnefextra
    have hbigm : CartierIsBig K (r • (m • D) - D') := by
      rw [hsplit]
      exact cartierIsBig_add_of_isNef_on_projective hdim hn hnorm hJ hbig hnefextra
    simpa only [cartierPullback_nsmul, add_comm] using
      (hvan (m • D) hnefm hbigm).1 (q + 1) (by omega)
  obtain ⟨N, hN⟩ := effective_twist_eventually_exists_nonzero_section_of_vanishing K
    (etaleChart_topologicalKrullDim cT) hn A hA (cartierPullback p D) E hE 0
    (fun m _ q => hvanm m q)
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨t, ht⟩ := hN m hm
  obtain ⟨e⟩ := hpush (m • D)
  have hex : ∃ t : Γ((cartierPullback p (m • D) + E).sheaf, ⊤), t ≠ 0 := by
    rw [cartierPullback_nsmul, add_comm]
    exact ⟨t, ht⟩
  obtain ⟨t, ht⟩ := hex
  exact ⟨Scheme.Modules.Hom.app e.inv ⊤ t, modulesIso_inv_app_top_ne_zero e t ht⟩

/-- Klt nonvanishing from nef and big adjoint positivity. -/
theorem klt_nef_eventually_nonzero_section
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (hcov : CodimOneChartCovered n K X)
    (hproj : ∃ J : CartierDivisor X, CartierIsAmpleProj K J)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective c₀ f₀ r D')
    (hklt : LogPairIsKlt c₀ f₀ r D') (D : CartierDivisor X) (hD : CartierIsNef K D) (a : ℕ)
    (hnef : CartierIsNef K ((r * a) • D - D')) (hbig : CartierIsBig K ((r * a) • D - D')) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ s : Γ((m • D).sheaf, ⊤), s ≠ 0 := by
  let : IsProper (X ↘ Spec (CommRingCat.of K)) :=
    isProper_structureMap_of_exists_ample_cartier hproj
  obtain ⟨J, hJ⟩ := hproj
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    exact ⟨a + 1, fun m hm => cartierIsGloballyGenerated_exists_nonzero_section
      (linearEffectiveFreeness_normalCurve hdim hnorm ⟨J, hJ⟩ c₀ f₀ r hr D' heff D hD a hbig m hm)⟩
  by_cases hzero : cartierNumericalDimension K n hdim D J = 0
  · exact klt_nef_numericalZero_eventually_nonzero_section K hdim hn hnorm hcov J hJ c₀ f₀ r hr
      D' heff hklt D hD a hnef hbig hzero
  obtain ⟨d₃, b₃, hd₃, D₃, η, hproper, heff₃, hlc₃, hcenter, hNK, hamp₃, hdimZ, hzeroZ, hLift⟩ :=
    original_klt_BPF_positive_numerical_constructs_isolated_restricted_zero_center_and_lifting K n
      hdim hn2 hnorm c₀ f₀ r hr D' heff hklt D hD a hnef hbig J hJ (by omega)
  let := hproper
  exact klt_isolated_numericallyTrivial_center_eventually_nonzero_section K hdim hn2 hnorm hcov
    J hJ c₀ f₀ r hr D' heff hklt D hD a hnef d₃ hd₃ D₃ heff₃ hlc₃ η hNK b₃ hamp₃
    (curve_into_pointClosure_pullbackDegree_eq_zero K ⟨J, hJ⟩ D hD η hzeroZ)

end MixedFujita
