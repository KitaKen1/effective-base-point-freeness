/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltBasePointFreeIitakaCases
public import MixedFujita.SNCComponentRestrictedFamily
public import MixedFujita.GlobalSNCComponentAdjunction
public import MixedFujita.SNCNefBigPointwiseVanishing
public import MixedFujita.AmpleCartierPullbackRepresentatives
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.SignedCartierPullbackSums
public import MixedFujita.CartierPullbackDegreeComparison
public import MixedFujita.SNCStratumIntegralNeighbourhoods
public import MixedFujita.SNCComponentEtaleAtlas
public import MixedFujita.EffectiveCartierPullbackTriviality
public import MixedFujita.DVRSupportPositiveCartierCoefficient

/-!
Nonvanishing on the unique lc place (step 16E).

On the round-up model of step 16D let S be the unique lc place, P the pullback of the nef divisor
D, and E the exceptional round-up. The restriction of P to S is numerically trivial. For all
large b the line bundle (b P + E)|_S has a nonzero section.

* S is a smooth projective (n − 1)-fold (an integral piece of the SNC stratum of S, with the
  étale charts of the component atlas).
* By adjunction K_S = (K_T + S)|_S, and the fractional part R = B + d_T (E − S) of the boundary
  restricts to an SNC boundary on S with coefficients in [0, d_T) (the restricted family).
* The adjoint d_T ((b P + E)|_S − K_S) − R|_S is the restriction of the ample
  d_T (b P − K_T) − B for b ≥ b₀; at b = 0 it differs from the case b = b₀ by a numerically
  trivial divisor, so it is ample by nef plus ample. Kawamata–Viehweg vanishing on S gives
  h^q((b P + E)|_S) = 0 for q ≥ 1 at b = 0 and all b ≥ b₀.
* The Euler polynomial χ(S, (b P + E)|_S) is then nonzero at b = 0, where it is h⁰(E|_S) ≥ 1
  (E|_S is effective), hence nonzero for all large b, where it equals h⁰.

No numerical invariance of the Euler characteristic is used.
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

/-- **Euler polynomial nonvanishing for an effective twist.** On an integral projective variety,
if the higher cohomology of E + b P vanishes at b = 0 and for all b ≥ b₀, and E is effective,
then E + b P has a nonzero section for all large b. -/
theorem effective_twist_eventually_exists_nonzero_section_of_vanishing
    (K : Type u) [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
    {ℓ : ℕ} (hdim : topologicalKrullDim Y = ℓ) (hℓ : 1 ≤ ℓ)
    (H : CartierDivisor Y) (hH : CartierIsAmpleProj K H)
    (P E : CartierDivisor Y) (hE : E.IsEffective) (b₀ : ℕ)
    (hvan : ∀ b : ℕ, (b = 0 ∨ b₀ ≤ b) → ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (E + b • P).sheaf (q + 1))) :
    ∃ N : ℕ, ∀ b : ℕ, N ≤ b → ∃ t : Γ((E + b • P).sheaf, ⊤), t ≠ 0 := by
  set Pol := cartierEulerPolynomial K ℓ P E with hPoldef
  have hPeval : ∀ b : ℕ, Pol.eval (b : ℚ) = (Scheme.Modules.eulerChar
      (Y ↘ Spec (CommRingCat.of K)) (E + b • P).sheaf : ℚ) := by
    intro b
    have h := proper_cartierEulerPolynomial_eval_int K ℓ hdim.le P E (b : ℤ)
    simpa only [Int.cast_natCast, natCast_zsmul] using h
  have hPol : Pol ≠ 0 := by
    intro hz
    obtain ⟨s, hs, -, -⟩ := effectiveCartier_exists_canonical_section_with_exact_nonvanishing
      (K := K) E hE
    have h0 : (E + (0 : ℕ) • P) = E := by rw [zero_smul, add_zero]
    have hχ := moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero K
      (E + (0 : ℕ) • P).sheaf (hvan 0 (Or.inl rfl))
    let : FiniteDimensional K Γ((E + (0 : ℕ) • P).sheaf, ⊤) :=
      cartier_finiteDimensional_sections_of_ample hdim hℓ hH _
    have hne : ∃ t : Γ((E + (0 : ℕ) • P).sheaf, ⊤), t ≠ 0 := by
      rw [h0]
      exact ⟨s, hs⟩
    obtain ⟨t, ht⟩ := hne
    have hpos : 0 < Module.finrank K Γ((E + (0 : ℕ) • P).sheaf, ⊤) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨t, ht⟩
    have hev := hPeval 0
    rw [hz, Polynomial.eval_zero, hχ] at hev
    have h00 : Module.finrank K Γ((E + (0 : ℕ) • P).sheaf, ⊤) = 0 := by
      exact_mod_cast hev.symm
    omega
  obtain ⟨N, hN⟩ := rationalPolynomial_eventually_eval_nat_ne_zero Pol hPol
  refine ⟨max N b₀, fun b hb => ?_⟩
  apply moduleSections_exists_nonzero_of_eulerChar_ne_zero K _ ?_
    (hvan b (Or.inr (le_of_max_le_right hb)))
  intro hz
  apply hN b (le_of_max_le_left hb)
  rw [hPeval b, hz, Int.cast_zero]

/-- Sections over the whole scheme are seen on the open piece U = ⊤. -/
theorem modulePullback_open_top_section_exists_ne_zero {Z Y : Scheme.{u}} (V : Z.Opens)
    (hV : V = ⊤) (g : Z ⟶ Y) (M : Y.Modules)
    (t : Γ((Scheme.Modules.pullback (V.ι ≫ g)).obj M, ⊤)) (ht : t ≠ 0) :
    ∃ s : Γ((Scheme.Modules.pullback g).obj M, ⊤), s ≠ 0 := by
  let N := (Scheme.Modules.pullback g).obj M
  let e : (Scheme.Modules.pullback (V.ι ≫ g)).obj M ≅ N.restrict V.ι :=
    ((Scheme.Modules.pullbackComp V.ι g).app M).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm
  have hu : Scheme.Modules.Hom.app e.hom ⊤ t ≠ 0 := modulesIso_hom_app_top_ne_zero e t ht
  have himg : V.ι ''ᵁ ⊤ = ⊤ := by rw [Scheme.Opens.ι_image_top, hV]
  have key : ∀ (W : Z.Opens), W = ⊤ → ∀ w : Γ(N, W), w ≠ 0 → ∃ s : Γ(N, ⊤), s ≠ 0 := by
    rintro W rfl w hw
    exact ⟨w, hw⟩
  exact key (V.ι ''ᵁ ⊤) himg (Scheme.Modules.Hom.app e.hom ⊤ t) hu

/-- An integral multiple of an effective divisor by a nonnegative integer is effective. -/
theorem zsmul_isEffective_of_nonneg {X : Scheme.{u}} [IsIntegral X] {D : CartierDivisor X}
    (hD : D.IsEffective) {c : ℤ} (hc : 0 ≤ c) : (c • D).IsEffective := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hc
  rw [natCast_zsmul]
  exact nsmul_isEffective_of_isEffective hD m

/-- A finite nonnegative integral combination of effective divisors is effective. -/
theorem finset_zsmul_sum_isEffective {X : Scheme.{u}} [IsIntegral X] {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (D : ι → CartierDivisor X) (hc : ∀ i ∈ s, 0 ≤ c i)
    (hD : ∀ i ∈ s, (D i).IsEffective) : (∑ i ∈ s, c i • D i).IsEffective := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CartierDivisor.isEffective_zero
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    exact (zsmul_isEffective_of_nonneg (hD i (Finset.mem_insert_self i s))
      (hc i (Finset.mem_insert_self i s))).add
      (ih (fun k hk => hc k (Finset.mem_insert_of_mem hk))
        (fun k hk => hD k (Finset.mem_insert_of_mem hk)))

/-- The fractional numerator of a round-up: 0 ≤ x + d ⌈−x/d⌉ < d. -/
theorem int_add_mul_ceil_neg_div_bounds (x : ℤ) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ x + (d : ℤ) * ⌈-((x : ℝ) / (d : ℝ))⌉ ∧ x + (d : ℤ) * ⌈-((x : ℝ) / (d : ℝ))⌉ < d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set c := ⌈-((x : ℝ) / (d : ℝ))⌉ with hcdef
  have h1 : -((x : ℝ) / (d : ℝ)) ≤ c := Int.le_ceil _
  have h2 : (c : ℝ) < -((x : ℝ) / (d : ℝ)) + 1 := Int.ceil_lt_add_one _
  have h1' : 0 ≤ (x : ℝ) + (d : ℝ) * c := by
    have := mul_le_mul_of_nonneg_left h1 hd0.le
    rw [mul_neg, mul_div_cancel₀ _ hd0.ne'] at this
    linarith
  have h2' : (x : ℝ) + (d : ℝ) * c < d := by
    have := mul_lt_mul_of_pos_left h2 hd0
    rw [mul_add, mul_neg, mul_div_cancel₀ _ hd0.ne', mul_one] at this
    linarith
  constructor
  · exact_mod_cast h1'
  · exact_mod_cast h2'

/-- **Nonvanishing on the unique lc place (step 16E).** On the round-up model of step 16D, with
S = ξ i₀ the unique lc place, E effective with no S-component, R = B + d_T (E − S) the
fractional numerator (B(S) = d_T), ample adjoints d_T (b P − K_T) − B for all b ≥ b₀, and P of
degree zero on every curve in S, the restriction of b P + E to S has a nonzero section for all
large b. -/
theorem klt_unique_place_eventually_restricted_section
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 2 ≤ n)
    {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] [IsNoetherian T]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))]
    (cT : EtaleChart K T n) {R : ℕ} (ξ : Fin R → T) (i₀ : Fin R)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (hJ : ∃ J : CartierDivisor T, CartierIsAmpleProj K J)
    (P B E S : CartierDivisor T) (hE : E.IsEffective) (hS : S.IsEffective) (dT b₀ : ℕ)
    (hE₀ : cartierCoefficient E (ξ i₀) = 0)
    (hSI : effectiveCartierIdealSheaf S hS = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i₀} : Set T), isClosed_closure⟩ : Closeds T))
    (hdT : 1 ≤ dT)
    (hBsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient B (t : T) = 0)
    (hround : ∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
      ⌈-((cartierCoefficient B (t : T) : ℝ) / (dT : ℝ))⌉)
    (hB₀ : cartierCoefficient B (ξ i₀) = dT)
    (hamp : ∀ b : ℕ, b₀ ≤ b →
      CartierIsAmpleProj K (dT • (b • P - smoothCanonicalDivisor cT) - B))
    (hP : ∀ (C : Scheme.{u}) [IsIntegral C] [C.Over (Spec (CommRingCat.of K))]
      [IsProper (C ↘ Spec (CommRingCat.of K))] [Smooth (C ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim C = 1 → ∀ φ : C ⟶ T,
        φ ≫ (T ↘ Spec (CommRingCat.of K)) = C ↘ Spec (CommRingCat.of K) →
        Set.range φ ⊆ closure ({ξ i₀} : Set T) → cartierCurvePullbackDegree (K := K) P φ = 0) :
    ∃ N : ℕ, ∀ b : ℕ, N ≤ b →
      ∃ t : Γ((Scheme.Modules.pullback (effectiveCartierIdealSheaf S hS).subschemeι).obj
        (b • P + E).sheaf, ⊤), t ≠ 0 := by
  classical
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ x : T, IsIntegrallyClosed (T.presheaf.stalk x) :=
    fun x => smooth_stalk_isIntegrallyClosed (K := K) x
  obtain ⟨J, hJamp⟩ := hJ
  -- the dimension of the stratum
  have hcard : Fintype.card ({i₀} : Finset (Fin R)) = 1 := by simp
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, n = Fintype.card ({i₀} : Finset (Fin R)) + ℓ := ⟨n - 1, by omega⟩
  subst hℓ
  have hℓ1 : 1 ≤ ℓ := by omega
  have hζ := sncSelectedPoints_isSNCFamily ξ hsnc {i₀}
  let I := sncStratumIdeal (sncDivisorFamilyOfPoints (sncSelectedPoints ξ {i₀})) Finset.univ
  let : I.subscheme.Over (Spec (CommRingCat.of K)) :=
    ⟨I.subschemeι ≫ (T ↘ Spec (CommRingCat.of K))⟩
  let : I.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hIeq : I = Scheme.IdealSheafData.vanishingIdeal
      (⟨closure ({ξ i₀} : Set T), isClosed_closure⟩ : Closeds T) :=
    sncStratumIdeal_selected_singleton_eq ξ i₀
  have hrange : Set.range I.subschemeι = closure ({ξ i₀} : Set T) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hIeq,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨y₀, -⟩ : ξ i₀ ∈ Set.range I.subschemeι := by
    rw [hrange]
    exact subset_closure rfl
  obtain ⟨U, -, hyU, -, -, hclosed, hint, hj⟩ :=
    snc_stratum_exists_lifted_integral_component (sncSelectedPoints ξ {i₀}) hζ y₀
  let := hint
  let := hj
  -- the open piece is the whole stratum
  have hUtop : U = ⊤ := by
    have hpre : _root_.IsPreconnected (Set.univ : Set I.subscheme) := by
      rw [← I.subschemeι.isClosedEmbedding.isInducing.isPreconnected_image, Set.image_univ,
        hrange]
      exact isPreconnected_singleton.closure
    let : PreconnectedSpace I.subscheme := ⟨hpre⟩
    have h := IsClopen.eq_univ ⟨hclosed, U.isOpen⟩ ⟨y₀, hyU⟩
    exact SetLike.coe_injective (h.trans (Opens.coe_top).symm)
  -- the closed immersion of the lc place and its instances
  let j := U.ι ≫ I.subschemeι
  have hjover : j ≫ (T ↘ Spec (CommRingCat.of K)) = U.toScheme ↘ Spec (CommRingCat.of K) := by
    simp only [j, Category.assoc]
    rfl
  let : j.IsOver (Spec (CommRingCat.of K)) := ⟨hjover⟩
  let : IsProper (U.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← hjover]
    infer_instance
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian j
  let : NoetherianSpace U.toScheme := j.isClosedEmbedding.isInducing.noetherianSpace
  let : IsNoetherian U.toScheme := {}
  -- the SNC members and their induced divisors on the lc place
  obtain ⟨Ec, hEc, hIc, hEcoef, G, hG, hsel, hunsel⟩ :=
    snc_component_exists_induced_effective_members ξ hξ hsnc {i₀} U
  have hSEc : S = Ec i₀ :=
    effectiveCartier_eq_of_idealSheaf_eq S (Ec i₀) hS (hEc i₀) (hSI.trans (hIc i₀).symm)
  -- charts and smoothness of the lc place
  let Es : Fin (Fintype.card ({i₀} : Finset (Fin R))) → CartierDivisor T :=
    fun k => Ec ((Fintype.equivFin ({i₀} : Finset (Fin R))).symm k).val
  have hEs : ∀ k, (Es k).IsEffective := fun k => hEc _
  have hIs : ∀ k, effectiveCartierIdealSheaf (Es k) (hEs k) =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({sncSelectedPoints ξ {i₀} k} : Set T), isClosed_closure⟩ : Closeds T) :=
    fun k => hIc _
  have hcover := snc_component_etaleChart_cover (sncSelectedPoints ξ {i₀}) hζ Es hEs U hclosed
  have hgeneric : genericPoint U ∈ iSup (fun c : EtaleChart K U ℓ => c.U) := by
    rw [hcover]
    trivial
  obtain ⟨cU, -⟩ := Opens.mem_iSup.mp hgeneric
  have hdimU : topologicalKrullDim U.toScheme = ℓ := etaleChart_topologicalKrullDim cU
  have hsmI : Smooth (I.subschemeι ≫ (T ↘ Spec (CommRingCat.of K))) :=
    Hironaka.Sequence.smooth_of_hasSncWith (T ↘ Spec (CommRingCat.of K))
      (sncStratumIdeal_hasSncWith _ (sncDivisorFamilyOfPoints_isSnc (K := K) _ hζ) Finset.univ)
  let : Smooth (U.toScheme ↘ Spec (CommRingCat.of K)) := by
    change Smooth (U.ι ≫ (I.subschemeι ≫ (T ↘ Spec (CommRingCat.of K))))
    infer_instance
  let : SmoothOfRelativeDimension ℓ (U.toScheme ↘ Spec (CommRingCat.of K)) :=
    TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_of_topologicalKrullDim_eq _ hdimU
  -- adjunction
  let KU := canonicalDivisor ℓ cU hcover
  have hEsSum : (∑ k, Es k) = S := by
    rw [sncSelectedPoints_cartier_sum Ec {i₀}, Finset.sum_singleton, hSEc]
  let aK : (Scheme.Modules.pullback j).obj (smoothCanonicalDivisor cT + S).sheaf ≅ KU.sheaf :=
    (Scheme.Modules.pullback j).mapIso
      (eqToIso (congrArg (fun D : CartierDivisor T => (smoothCanonicalDivisor cT + D).sheaf)
        hEsSum.symm)) ≪≫
      sncComponentGlobalAdjunctionIso (sncSelectedPoints ξ {i₀}) Es U hclosed hζ hEs hIs cT
        etaleCharts_cover cU
  -- the fractional numerator Rf of the boundary
  let Rf := B + dT • (E - S)
  have hRcoef : ∀ t : CodimensionOnePoint T, cartierCoefficient Rf (t : T) =
      cartierCoefficient B (t : T) +
        (dT : ℤ) * ⌈-((cartierCoefficient B (t : T) : ℝ) / (dT : ℝ))⌉ := by
    intro t
    simp only [Rf, cartierCoefficient_add, cartierCoefficient_nsmul, hround t]
  have hSoff : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient S (t : T) = 0 := by
    intro t ht
    rw [hSEc, hEcoef i₀ t, if_neg (fun h => ht ⟨i₀, h.symm⟩)]
  have hRsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient Rf (t : T) = 0 := by
    intro t ht
    rw [hRcoef t, hBsupp t ht]
    simp
  have hEsupp : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient E (t : T) = 0 := by
    intro t ht
    have h := hround t
    rw [hBsupp t ht, cartierCoefficient_sub, hSoff t ht] at h
    simpa using h
  have hRzero : ∀ i ∈ ({i₀} : Finset (Fin R)), cartierCoefficient Rf (ξ i) = 0 := by
    intro i hi
    rw [Finset.mem_singleton.mp hi, hRcoef ⟨ξ i₀, hξ i₀⟩, hB₀]
    have hd0 : (dT : ℝ) ≠ 0 := by exact_mod_cast (show dT ≠ 0 by omega)
    have : -(((dT : ℤ) : ℝ) / (dT : ℝ)) = ((-1 : ℤ) : ℝ) := by
      push_cast
      rw [div_self hd0]
    rw [this, Int.ceil_intCast]
    ring
  have hEzero : ∀ i ∈ ({i₀} : Finset (Fin R)), cartierCoefficient E (ξ i) = 0 := by
    intro i hi
    rw [Finset.mem_singleton.mp hi, hE₀]
  have hRbd : ∀ i, 0 ≤ cartierCoefficient Rf (ξ i) ∧ cartierCoefficient Rf (ξ i) < dT := by
    intro i
    rw [hRcoef ⟨ξ i, hξ i⟩]
    exact int_add_mul_ceil_neg_div_bounds _ hdT
  -- the restrictions of Rf, E and P
  have hGiso : ∀ i, i ∉ ({i₀} : Finset (Fin R)) →
      Nonempty ((Scheme.Modules.pullback j).obj (Ec i).sheaf ≅ (G i).sheaf) :=
    fun i hi => (hunsel i hi).2.1
  obtain ⟨aR⟩ := supported_cartier_induced_signed_sum_representation hnormT j ξ hinj Ec hEcoef Rf
    hRsupp {i₀} hRzero G hGiso
  obtain ⟨aE⟩ := supported_cartier_induced_signed_sum_representation hnormT j ξ hinj Ec hEcoef E
    hEsupp {i₀} hEzero G hGiso
  set F := ∑ i ∈ ({i₀} : Finset (Fin R))ᶜ, cartierCoefficient Rf (ξ i) • G i with hFdef
  set EU := ∑ i ∈ ({i₀} : Finset (Fin R))ᶜ, cartierCoefficient E (ξ i) • G i with hEUdef
  have hEU : EU.IsEffective :=
    finset_zsmul_sum_isEffective _ _ _
      (fun i _ => cartierCoefficient_nonneg_of_isEffective E hE (ξ i)) (fun i _ => hG i)
  obtain ⟨PU, ⟨aP⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor P j
  -- P is numerically trivial on the lc place
  have hrangej : Set.range j ⊆ closure ({ξ i₀} : Set T) := by
    rw [← hrange]
    rintro _ ⟨y, rfl⟩
    exact ⟨U.ι y, rfl⟩
  have hPU : CartierIsNumericallyTrivial K PU := by
    intro C _ _ _ _ hC ψ hψ
    rw [← cartierCurvePullbackDegree_comp_of_representation hC j ψ P PU aP]
    apply hP C hC (ψ ≫ j)
    · rw [Category.assoc, hjover, hψ]
    · rintro _ ⟨c, rfl⟩
      exact hrangej ⟨ψ c, rfl⟩
  -- the coefficients of F on the lc place
  have hreg : ∀ y : U.toScheme, IsRegularLocalRing (U.toScheme.presheaf.stalk y) :=
    fun y => isRegularLocalRing_stalk (U.toScheme ↘ Spec (CommRingCat.of K)) y
  have hGI : ∀ i, i ≠ i₀ → effectiveCartierIdealSheaf (G i) (hG i) =
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i} : Set T), isClosed_closure⟩ : Closeds T)).comap j := by
    intro i hi
    rw [(hunsel i (by simpa using hi)).1, hIc i]
  have hcoefG := snc_selected_singleton_induced_coefficient (K := K) ξ hsnc i₀ U hreg G hG hGI
  have hFcoef : ∀ t : CodimensionOnePoint U, 0 ≤ cartierCoefficient F t.1 ∧
      cartierCoefficient F t.1 < dT ∧
      (cartierCoefficient F t.1 ≠ 0 → ∃ i, i ≠ i₀ ∧ j t.1 ∈ closure ({ξ i} : Set T)) := by
    intro t
    obtain ⟨hc1, hc2⟩ := hcoefG t
    have hsum : cartierCoefficient F t.1 = ∑ i ∈ ({i₀} : Finset (Fin R))ᶜ,
        cartierCoefficient Rf (ξ i) * cartierCoefficient (G i) t.1 := by
      rw [hFdef, cartierCoefficient_sum]
      simp only [cartierCoefficient_zsmul]
    by_cases hex : ∃ i, i ≠ i₀ ∧ j t.1 ∈ closure ({ξ i} : Set T)
    · obtain ⟨i₁, hi₁, hti₁⟩ := hex
      have hval : cartierCoefficient F t.1 = cartierCoefficient Rf (ξ i₁) := by
        rw [hsum, Finset.sum_eq_single i₁]
        · rw [hc1 i₁ hi₁, if_pos hti₁, mul_one]
        · intro i hi hne
          have hi' : i ≠ i₀ := by simpa using hi
          rw [hc1 i hi', if_neg (fun h => hne (hc2 i i₁ hi' hi₁ h hti₁)), mul_zero]
        · intro h
          exact absurd (by simpa using hi₁) h
      rw [hval]
      exact ⟨(hRbd i₁).1, (hRbd i₁).2, fun _ => ⟨i₁, hi₁, hti₁⟩⟩
    · push_neg at hex
      have hval : cartierCoefficient F t.1 = 0 := by
        rw [hsum]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi' : i ≠ i₀ := by simpa using hi
        rw [hc1 i hi', if_neg (hex i hi'), mul_zero]
      rw [hval]
      exact ⟨le_rfl, by exact_mod_cast hdT, fun h => absurd rfl h⟩
  -- the restricted SNC family on the lc place
  have havoid : ∀ i, i ≠ i₀ → j (genericPoint U) ∉ closure ({ξ i} : Set T) :=
    fun i hi => snc_component_generic_avoids_unselected ξ hsnc {i₀} U i (by simpa using hi)
  obtain ⟨r', ζ', hinj', hζ', hsnc', hrng⟩ :=
    snc_selected_singleton_exists_restricted_snc_family (K := K) (ℓ := ℓ) ξ hsnc i₀ U havoid
  have hFsupp : ∀ t : CodimensionOnePoint U, (t : U.toScheme) ∉ Set.range ζ' →
      cartierCoefficient F (t : U.toScheme) = 0 := by
    intro t ht
    by_contra hne
    obtain ⟨i, hi, hti⟩ := (hFcoef t).2.2 hne
    exact ht (hrng t i hi hti)
  have hF0 : ∀ t : CodimensionOnePoint U,
      cartierCoefficient (0 : CartierDivisor U) (t : U.toScheme) =
        ⌈-((cartierCoefficient F (t : U.toScheme) : ℝ) / (dT : ℝ))⌉ := by
    intro t
    rw [cartierCoefficient_zero]
    obtain ⟨h0, h1, -⟩ := hFcoef t
    have hd0 : (0 : ℝ) < dT := by exact_mod_cast hdT
    have hx0 : (0 : ℝ) ≤ (cartierCoefficient F t.1 : ℝ) / dT := div_nonneg (by exact_mod_cast h0) hd0.le
    have hx1 : (cartierCoefficient F t.1 : ℝ) / dT < 1 := by
      rw [div_lt_one hd0]
      exact_mod_cast h1
    symm
    rw [Int.ceil_eq_iff]
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  -- an ample divisor on the lc place
  obtain ⟨HU, hHU, -⟩ := finite_integral_source_exists_ample_cartier_representative K j J hJamp
  -- the restricted line bundles and adjoints
  have hQiso : ∀ b : ℕ, Nonempty ((Scheme.Modules.pullback j).obj (b • P + E).sheaf ≅
      (EU + b • PU).sheaf) := by
    intro b
    exact ⟨(Scheme.Modules.pullback j).mapIso (cartierTensorSheafIso (b • P) E).symm ≪≫
      cartierPullbackTensorIso (b • P) j E.sheaf ≪≫
      MonoidalCategory.tensorIso (cartierPullbackGradedIso P j PU aP b) aE ≪≫
      cartierTensorSheafIso (b • PU) EU ≪≫
      eqToIso (congrArg CartierDivisor.sheaf (add_comm (b • PU) EU))⟩
  have hAiso : ∀ b : ℕ, Nonempty ((Scheme.Modules.pullback j).obj
      (dT • (b • P - smoothCanonicalDivisor cT) - B).sheaf ≅
      (dT • ((EU + b • PU) - KU) - F).sheaf) := by
    intro b
    let Ms : Fin 4 → CartierDivisor T := ![P, E, smoothCanonicalDivisor cT + S, Rf]
    let Gs : Fin 4 → CartierDivisor U := ![PU, EU, KU, F]
    let cs : Fin 4 → ℤ := ![((dT * b : ℕ) : ℤ), (dT : ℤ), -(dT : ℤ), -1]
    obtain ⟨a⟩ := cartierPullback_finset_signed_sum_of_member_isos j Finset.univ Ms Gs cs (by
      intro i _
      fin_cases i
      · exact ⟨aP⟩
      · exact ⟨aE⟩
      · exact ⟨aK⟩
      · exact ⟨aR⟩)
    have h1 : (∑ i ∈ Finset.univ, cs i • Ms i) = dT • (b • P - smoothCanonicalDivisor cT) - B := by
      simp only [Fin.sum_univ_four, Ms, cs, Rf, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      simp only [← natCast_zsmul, Nat.cast_mul]
      module
    have h2 : (∑ i ∈ Finset.univ, cs i • Gs i) = dT • ((EU + b • PU) - KU) - F := by
      simp only [Fin.sum_univ_four, Gs, cs, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      simp only [← natCast_zsmul, Nat.cast_mul]
      module
    exact ⟨(Scheme.Modules.pullback j).mapIso (eqToIso (congrArg CartierDivisor.sheaf h1.symm)) ≪≫
      a ≪≫ eqToIso (congrArg CartierDivisor.sheaf h2)⟩
  have hampU : ∀ b : ℕ, b₀ ≤ b → CartierIsAmpleProj K (dT • ((EU + b • PU) - KU) - F) := by
    intro b hb
    obtain ⟨a⟩ := hAiso b
    exact cartierIsAmpleProj_of_finite_pullback_over K j _ _ (hamp b hb) a
  have hampU0 : CartierIsAmpleProj K (dT • ((EU + (0 : ℕ) • PU) - KU) - F) := by
    have hN : CartierIsNef K (-((dT * b₀) • PU)) := by
      have := ((cartierIsNumericallyTrivial_iff_nef_and_neg_nef PU).mp hPU).2
      rw [← smul_neg]
      exact cartierIsNef_nsmul this _
    have h := nefAddAmpleStatement_holds K U.toScheme _ _ hN (hampU b₀ le_rfl)
    have heq : -((dT * b₀) • PU) + (dT • ((EU + b₀ • PU) - KU) - F) =
        dT • ((EU + (0 : ℕ) • PU) - KU) - F := by
      simp only [← natCast_zsmul, Nat.cast_mul, Nat.cast_zero]
      module
    rwa [heq] at h
  -- Kawamata–Viehweg vanishing on the lc place
  have hvan : ∀ b : ℕ, (b = 0 ∨ b₀ ≤ b) → ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (EU + b • PU).sheaf (q + 1)) := by
    intro b hb q
    have hA : CartierIsAmpleProj K (dT • ((EU + b • PU) - smoothCanonicalDivisor cU) - F) := by
      rcases hb with rfl | hb
      · exact hampU0
      · exact hampU b hb
    have hnef := cartierIsAmpleProj_isNef hA
    have hbig := cartierIsAmpleProj_isBig hdimU hℓ1 hA
    have h := signed_snc_roundup_nef_big_higher_vanishing_of_charZero K HU hHU cU ζ' hinj' hζ'
      hsnc' F 0 (EU + b • PU) dT hdT hFsupp hF0 hnef hbig (q + 1) (by omega)
    simpa only [add_zero] using h
  -- nonvanishing by the Euler polynomial, and transport to the lc place
  obtain ⟨N, hN⟩ := effective_twist_eventually_exists_nonzero_section_of_vanishing K hdimU hℓ1
    HU hHU PU EU hEU b₀ hvan
  refine ⟨N, fun b hb => ?_⟩
  obtain ⟨tU, htU⟩ := hN b hb
  obtain ⟨aQ⟩ := hQiso b
  have ht : Scheme.Modules.Hom.app aQ.inv ⊤ tU ≠ 0 := modulesIso_inv_app_top_ne_zero aQ tU htU
  obtain ⟨t, ht'⟩ := modulePullback_open_top_section_exists_ne_zero U hUtop I.subschemeι
    (b • P + E).sheaf _ ht
  have hSI' : effectiveCartierIdealSheaf S hS = I := hSI.trans hIeq.symm
  rw [hSI']
  exact ⟨t, ht'⟩

end MixedFujita
