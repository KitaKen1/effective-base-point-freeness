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

/-!
The removal of points of stable base loci, the base point free theorem and F2 (step 16F).

Let D be nef with (r a) D − (K_X + Δ) nef and big for a klt pair, with nonzero sections of all
large multiples, and let the base locus of b^e D be nonempty. Then:

* the base locus contains an isolated lc centre W on which D is numerically trivial (step 16W);
* on a model with an SNC round-up, W has a unique lc place S over it (step 16D);
* (b P + E)|_S has nonzero sections for all large b, P the pullback of D (step 16E);
* such a section generates somewhere on the reduced S and lifts, by Kawamata–Viehweg vanishing on
  the model, to a section of b D not vanishing at a point of W (the lifting of the X-method).

So some larger power b^f D is generated at a point of the base locus of b^e D. This is the removal
statement; with it the base point free theorem for divisors with an Iitaka dimension holds, and F2
(linear effective freeness) follows.
-/

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

/-- **Removal of a point of the stable base locus (step 16F).** -/
theorem kltStableBaseLocusRemovalStatement_holds : KltStableBaseLocusRemovalStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ _ n hdim hn hnorm hcov J hJ c₀ f₀ r hr D' heff hklt D hD a _ha
    hnefa hbig N hN _hν b hb e he _hstab hne
  -- a nonzero section of b^e D
  obtain ⟨s₀, hs₀⟩ := hN (b ^ e) he
  -- the isolated numerically trivial lc centre in the base locus
  obtain ⟨d₃, hd₃, D₃, η, b₃, heff₃, hlc₃, -, hNK, hamp₃, hWBs, hdeg⟩ :=
    klt_base_locus_exists_isolated_numericallyTrivial_center K hdim hn hnorm hcov J hJ c₀ f₀ r hr
      D' heff hklt D hD a hnefa hbig (b ^ e) s₀ hs₀ hne
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
  -- a large power
  set f := e + (N₁ + b₀) with hfdef
  have hpow : N₁ + b₀ ≤ b ^ f := by
    have h1 : f < b ^ f := Nat.lt_pow_self (by omega)
    omega
  obtain ⟨t, ht⟩ : ∃ t : Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj
      (cartierPullback p ((b ^ f) • D) + E).sheaf, ⊤), t ≠ 0 := by
    rw [cartierPullback_nsmul]
    exact hN₁ (b ^ f) (by omega)
  -- the section generates somewhere on the reduced place
  let : IsReduced (effectiveCartierIdealSheaf S hS).subscheme :=
    hSI ▸ Hironaka.Resolution.isReduced_subscheme_vanishingIdeal _
  obtain ⟨z, W, hzW, a, hunit⟩ := nonzero_invertible_section_generates_somewhere_on_reduced _
    (cartierPullbackSheaf_isInvertible _ _) t ht
  -- the lifting
  have hA := hampT (b ^ f) (by omega)
  have hx := original_basepoint_removed_of_usual_KV_snc_roundup_cut K
    (kawamataViehwegVanishingSNC_of_charZero K n) p hp hnorm J hJ ((b ^ f) • D) cT ξ hinj hξ hsnc
    B E S hE hexc hS dT hdT hBsupp hround (cartierIsAmpleProj_isNef hA)
    (cartierIsAmpleProj_isBig hdimT (by omega) hA) z W hzW a t hunit
  refine ⟨f, p ((effectiveCartierIdealSheaf S hS).subschemeι z), by omega, ?_, hx⟩
  apply hWBs
  apply hpS
  have hz : (effectiveCartierIdealSheaf S hS).subschemeι z ∈
      Set.range (effectiveCartierIdealSheaf S hS).subschemeι := ⟨z, rfl⟩
  have hsupp : ((effectiveCartierIdealSheaf S hS).support : Set T) = closure ({ξ i₀} : Set T) := by
    rw [hSI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [Scheme.IdealSheafData.range_subschemeι, hsupp] at hz
  exact hz

/-- **The base point free theorem** for nef divisors with an Iitaka dimension on klt pairs. -/
theorem kltBasePointFreeIitakaStatement_holds : KltBasePointFreeIitakaStatement.{u} :=
  kltBasePointFreeIitakaStatement_of_removal kltStableBaseLocusRemovalStatement_holds

/-- **F2: linear effective freeness**, with no remaining hypotheses. -/
theorem linearEffectiveFreeness_proved : LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_basePointFreeIitaka kltBasePointFreeIitakaStatement_holds

end MixedFujita
