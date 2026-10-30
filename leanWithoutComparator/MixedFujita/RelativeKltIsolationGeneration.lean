/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RelativeIsolationNefBig
public import MixedFujita.RelativeNumericalFreenessStatement
public import MixedFujita.KltNumericalFreenessConditional
public import MixedFujita.SteinCartierSections
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.LinearEffectiveFreenessReduction
public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.LinearEffectiveFreenessRelative

/-!
Section 6 of the manuscript for relative K-NF (step 17R-1).

Let (V, B) be a projective klt pair with D = d(K_V + B), f : V → Y a contraction
(f_* O_V = O_Y), P and L Cartier divisors of Y with L ample and N_V = d f*P − D − f*L ample on V.
The data of the minimizer over a closed point y of Y (`RelIsolationMinimizerData`) are the data of
section 6 on a smooth proper simple normal crossing model π : X → V for the sections of multiples
of L pulled back to X, with the inequality (24) and the centre property for the fibre
π⁻¹(f⁻¹(y)) in place of the fibre over a point of V. Then:

* the lifting with the centre in a closed set (`exists_section_generating_of_minimizer_data_of_kv_of_open`)
  applies with L_X = π*f*L, N_X = π*N_V, the fibre Φ = f⁻¹(y) and V₀ = f⁻¹(U) for an open
  neighbourhood U of y with a local equation φ of P: the Kawamata–Viehweg theorem on the models of
  V gives a section of f*P generating it at a point of the fibre;
* the section descends along the Stein-type map f (`stein_exists_section_generating_of_pullback`)
  to a section of P generating it at y.

Hence relative K-NF follows from the existence of these data at the closed points at which P is
not generated (`RelMinimizerDataStatement`, the content of sections 2 to 5 and 7 relative to f),
and F2 from the base point free theorem and that statement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Descent

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  (g : T ⟶ X) [IsDominant g]
  (happ : ∀ U : X.Opens, Function.Surjective (g.app U).hom)

include happ

/-- Generation descends along a Stein-type morphism: if g*D has a global section generating it at
the point t with the pulled back local equation of D, then D has a global section generating it
at g t with that local equation. -/
theorem stein_exists_section_generating_of_pullback (D : CartierDivisor X) (t : T)
    (φ : X.functionFieldˣ) (hφ : D.IsLocalEquationAt (g t) φ)
    (r : T.functionField) (u : (T.presheaf.stalk t)ˣ)
    (hr : (rationalFunctionsEquiv (X := T) ⊤).symm r ∈ (cartierPullback g D).sections ⊤)
    (hu : algebraMap (T.presheaf.stalk t) T.functionField u =
      ((Units.map (dominantFunctionFieldMap g).hom.toMonoidHom φ : T.functionFieldˣ) :
        T.functionField) * r) :
    ∃ (s : X.functionField) (v : (X.presheaf.stalk (g t))ˣ),
      (rationalFunctionsEquiv (X := X) ⊤).symm s ∈ D.sections ⊤ ∧
      algebraMap (X.presheaf.stalk (g t)) X.functionField v = φ * s := by
  obtain ⟨s, hs⟩ := stein_cartier_section_rational_in_image g happ D (CartierDivisor.sectionMk _ hr)
  have hsr : (dominantFunctionFieldMap g).hom s = r := by
    rw [hs, cartierSectionRational_sectionMk]
  have hsD : (rationalFunctionsEquiv (X := X) ⊤).symm s ∈ D.sections ⊤ :=
    mem_sections_of_cartierPullback_of_open_app_surjective g happ D s (by rw [hsr]; exact hr)
  obtain ⟨a, ha⟩ := (CartierDivisor.mem_sections.mp hsD) (g t) trivial φ hφ
  rw [LinearEquiv.apply_symm_apply] at ha
  have hpull : (dominantFunctionFieldMap g).hom ((φ : X.functionField) * s) =
      algebraMap (T.presheaf.stalk t) T.functionField (g.stalkMap t a) := by
    rw [← ha, dominantFunctionFieldMap_algebraMap]
  have hau : g.stalkMap t a = (u : T.presheaf.stalk t) := by
    apply IsFractionRing.injective (T.presheaf.stalk t) T.functionField
    rw [← hpull, map_mul, hsr, hu]
    rfl
  have hunit : IsUnit a := by
    have hv' : IsUnit (g.stalkMap t a) := by rw [hau]; exact u.isUnit
    exact isUnit_of_map_unit (g.stalkMap t).hom a hv'
  exact ⟨s, hunit.unit, hsD, by rw [IsUnit.unit_spec]; exact ha⟩

end Descent

section Data

variable {K : Type u} [Field K] {n : ℕ} {V Y : Scheme.{u}}
  [IsIntegral V] [IsLocallyNoetherian V] [V.Over (Spec (CommRingCat.of K))]
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- The data of the minimizer over the closed point y of the base, in the form used by section 6
for relative K-NF: a degree j divisible by m₀, nonzero sections s_i of j f*L on X (the pullbacks of
the sections of j L on Y, f being a contraction), a smooth proper
simple normal crossing model π : X → V of the pair whose family supports the crepant boundary and
the pullbacks of the zero divisors of the s_i, and a positive vector c and a profile q with
c · q = 1 in the polytope of a point z of X over y, with the inequality (24) and the centre
property for the fibre π⁻¹(f⁻¹(y)) and the budget d j Σ c_i < 1. -/
def RelIsolationMinimizerData (cV : EtaleChart K V n) (fV : V.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor V) (f : V ⟶ Y) [IsDominant f] (L : CartierDivisor Y) (m₀ : ℕ) (y : Y) :
    Prop :=
  ∃ (j N : ℕ) (s : Fin N → Γ((j • cartierPullback f L).sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (X : Scheme.{u}) (_ : IsIntegral X) (_ : IsLocallyNoetherian X)
    (_ : X.Over (Spec (CommRingCat.of K))) (_ : IsProper (X ↘ Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K)))
    (π : X ⟶ V) (_ : IsDominant π) (_ : π.IsOver (Spec (CommRingCat.of K))) (_ : IsProper π)
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    (r : ℕ) (ξ : Fin r → X) (z : X) (c q : Fin N → ℝ),
    m₀ ∣ j ∧ Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
    (∀ w : CodimensionOnePoint X, (w : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) (w : X) =
        0) ∧
    (∀ i, ∀ w : CodimensionOnePoint X, (w : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) (w : X) = 0) ∧
    f (π z) = y ∧ (∀ i, 0 < c i) ∧ ∑ i, c i * q i = 1 ∧
    InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) q z ∧
    (∀ p ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)), InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) q p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) (ξ k)) / d) ∧
    (∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' (f ⁻¹' ({y} : Set Y))).Nonempty →
      InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) q p →
        p ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y))) ∧
    ((d * j : ℕ) : ℝ) * ∑ i, c i < 1

end Data

section Klt

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {V Y X : Scheme.{u}}
  [IsIntegral V] [IsLocallyNoetherian V] [V.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of K))]
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- Section 6 for relative K-NF: for a projective klt pair (V, B) with effective boundary,
D = d(K_V + B), a contraction f : V → Y and Cartier divisors P, L of Y with L ample, the multiples
of m₀ L globally generated and d f*P − D − f*L ample, the data of the minimizer over the closed
point y of Y on a simple normal crossing model π : X → V give a global section of P generating it
at y. -/
theorem rel_exists_section_generating_of_minimizer_data
    (hn : 1 ≤ n) (hdimV : topologicalKrullDim V = n)
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (hcov : CodimOneChartCovered n K V) {H : CartierDivisor V} (hH : CartierIsAmpleProj K H)
    (cV : EtaleChart K V n) (fV : V.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor V)
    (heff : LogPairBoundaryEffective cV fV d D) (hklt : LogPairIsKlt cV fV d D)
    (f : V ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
    (P L : CartierDivisor Y) (hL : CartierIsAmpleProj K L)
    (hN : CartierIsAmpleProj K (d • cartierPullback f P - D - cartierPullback f L))
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hLgg : ∀ k : ℕ, CartierIsGloballyGenerated ((k * m₀) • L))
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (j : ℕ) (hjm₀ : m₀ ∣ j) {Ns : ℕ} (s : Fin Ns → Γ((j • cartierPullback f L).sheaf, ⊤))
    (hs : ∀ i, s i ≠ 0)
    (π : X ⟶ V) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ w : CodimensionOnePoint X, (w : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) (w : X) = 0)
    (hDsupp : ∀ i, ∀ w : CodimensionOnePoint X, (w : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) (w : X) = 0)
    (z : X) (hz : f (π z) = y) {c q : Fin Ns → ℝ} (hc : ∀ i, 0 < c i) (hcq : ∑ i, c i * q i = 1)
    (hqz : InSNCProfilePolytope ξ d
      (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
      (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) q z)
    (hpolyΦ : ∀ p ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)), InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) q p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) (ξ k)) / d)
    (hcentre : ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' (f ⁻¹' ({y} : Set Y))).Nonempty →
      InSNCProfilePolytope ξ d
        (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) q p →
        p ∈ π ⁻¹' (f ⁻¹' ({y} : Set Y)))
    (hbudget : ((d * j : ℕ) : ℝ) * ∑ i, c i < 1) :
    ∃ (φ : Y.functionFieldˣ) (hφ : P.IsLocalEquationAt y φ) (t : Γ(P.sheaf, ⊤)),
      IsUnit (cartierLocalCoefficient P y φ hφ t) := by
  have hsmX : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormX : ∀ w : X, IsIntegrallyClosed (X.presheaf.stalk w) := fun w =>
    smooth_stalk_isIntegrallyClosed (K := K) w
  have hπ' : Function.Bijective (dominantFunctionFieldMap π).hom := hπ
  have hdim : topologicalKrullDim X = topologicalKrullDim V :=
    (etaleChart_topologicalKrullDim cX).trans hdimV.symm
  -- the boundary of X
  have hb : ∀ k, cartierCoefficient (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
      (ξ k) < (d : ℤ) := fun k =>
    logPairIsKlt_crepantBoundary_coefficient_lt π hπ cV fV d D hklt cX ⟨ξ k, hξ k⟩
  have hBexc : ∀ w : CodimensionOnePoint X, Order.coheight (π (w : X)) = 1 →
      0 ≤ cartierCoefficient (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover)
        (w : X) := by
    intro w hw
    have hbij := stalkMap_bijective_of_birational_over_normal_prime hnormV π hπ' (w : X) hw
    let := hnormV (π (w : X))
    have : IsDiscreteValuationRing (V.presheaf.stalk (π (w : X))) :=
      normal_codimensionOne_stalk_DVR (⟨π (w : X), hw⟩ : CodimensionOnePoint V)
    have : IsDiscreteValuationRing (X.presheaf.stalk (w : X)) :=
      smoothOverField_codimensionOne_stalk_DVR (K := K) w
    obtain ⟨c', hc'⟩ := hcov (π (w : X)) hw
    rw [crepantBoundaryCartier_coefficient_of_stalkMap_bijective π hπ cV fV d D cX w hw hbij c'
      hc']
    have h := heff c' (π (w : X)) hc' hw
    linarith
  -- the decomposition on X
  set NV := d • cartierPullback f P - D - cartierPullback f L with hNV
  have hLNV : d • cartierPullback f P - D = cartierPullback f L + NV := by
    rw [hNV]
    abel
  have hLNX : d • cartierPullback π (cartierPullback f P) -
      (d • (smoothCanonicalDivisor cX +
        principalCartierDivisor X (crepantPullbackFormUnit π hπ cV fV cX)) +
        crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) =
      cartierPullback π (cartierPullback f L) + cartierPullback π NV := by
    rw [crepantBoundaryCartier_smooth_recombine, ← cartierPullback_nsmul, ← cartierPullback_sub,
      hLNV, cartierPullback_add]
  -- the zero divisors
  have hDlin : ∀ i, ∃ h : X.functionFieldˣ,
      cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i)) =
        j • cartierPullback π (cartierPullback f L) + principalCartierDivisor X h := fun i =>
    ⟨_, by
      unfold cartierSectionZeroDivisor
      rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_principal]⟩
  have hDeff : ∀ i, (cartierPullback π
      (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))).IsEffective := fun i =>
    cartierPullback_isEffective π _ (cartierSectionZeroDivisor_isEffective _ (s i) (hs i))
  -- positivity on X
  have hLggX : ∀ k : ℕ, CartierIsGloballyGenerated
      ((k * m₀) • cartierPullback π (cartierPullback f L)) := fun k => by
    rw [← cartierPullback_nsmul, ← cartierPullback_nsmul]
    exact cartierIsGloballyGenerated_cartierPullback π _
      (cartierIsGloballyGenerated_cartierPullback f _ (hLgg k))
  have hNnefPull : ∀ (T' : Scheme.{u}) [IsIntegral T'] [T'.Over (Spec (CommRingCat.of K))]
      (ρ' : T' ⟶ X) [IsDominant ρ'] [ρ'.IsOver (Spec (CommRingCat.of K))],
      CartierIsNef K (cartierPullback ρ' (cartierPullback π NV)) := by
    intro T' _ _ ρ' _ _
    rw [← cartierPullback_comp π ρ' NV]
    exact cartierIsNef_cartierPullback_of_ample hH (cartierIsAmpleProj_isNef hN) (ρ' ≫ π)
  have hLnefV : CartierIsNef K (cartierPullback f L) :=
    cartierIsNef_cartierPullback_of_ample hL (cartierIsAmpleProj_isNef hL) f
  have hpullX : ∀ a b : ℕ, cartierPullback π (a • cartierPullback f L + b • NV) =
      a • cartierPullback π (cartierPullback f L) + b • cartierPullback π NV := fun a b => by
    rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_nsmul]
  have hABbig : ∀ a b : ℕ, 1 ≤ b →
      CartierIsBig K (a • cartierPullback π (cartierPullback f L) + b • cartierPullback π NV) := by
    intro a b hb'
    have hamp : CartierIsAmpleProj K (a • cartierPullback f L + b • NV) :=
      nefAddAmpleStatement_holds K V _ _ (cartierIsNef_nsmul hLnefV a)
        (cartierIsAmpleProj_nsmul hN hb')
    rw [← hpullX]
    exact cartierIsBig_cartierPullback hnormV hnormX π hπ hdim
      (cartierIsAmpleProj_isBig hdimV hn hamp)
  have hABfin : ∀ a b : ℕ, FiniteDimensional K
      Γ((a • cartierPullback π (cartierPullback f L) + b • cartierPullback π NV).sheaf, ⊤) := by
    intro a b
    rw [← hpullX]
    exact finiteDimensional_sections_cartierPullback hnormV π hπ _
      (cartier_finiteDimensional_sections_of_ample hdimV hn hH _)
  -- a local equation of P near y and the fibre
  obtain ⟨φ, hφ⟩ := P.exists_isLocalEquationAt y
  obtain ⟨U, hyU, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hφ
  have : Nonempty U := ⟨⟨y, hyU⟩⟩
  have hV₀ : ∀ v ∈ f ⁻¹ᵁ U, (cartierPullback f P).IsLocalEquationAt v
      (Units.map (dominantFunctionFieldMap f).hom.toMonoidHom φ) := fun v hv =>
    cartierPullback_isLocalEquationAt f P v
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU hv)
  have hΦ : IsClosed (f ⁻¹' ({y} : Set Y)) := hy.preimage f.continuous
  have hΦV₀ : f ⁻¹' ({y} : Set Y) ⊆ ((f ⁻¹ᵁ U : V.Opens) : Set V) := by
    intro v hv
    change f v ∈ U
    rw [show f v = y from hv]
    exact hyU
  obtain ⟨v, hv, g, u, hg, hu⟩ := exists_section_generating_of_minimizer_data_of_kv_of_open
    (kawamataViehwegVanishingSNC_of_charZero K n) hnormV π hπ' (cartierPullback f P)
    (f ⁻¹' ({y} : Set Y)) hΦ (Units.map (dominantFunctionFieldMap f).hom.toMonoidHom φ)
    (f ⁻¹ᵁ U) hΦV₀ hV₀ ξ hinj hξ hsnc cX (crepantPullbackFormUnit π hπ cV fV cX) d hd
    (crepantBoundaryCartier π hπ cV fV d D cX etaleCharts_cover) hBsupp hb hBexc
    (fun i => cartierPullback π (cartierSectionZeroDivisor (j • cartierPullback f L) (s i) (hs i))) hDeff hDsupp
    (cartierPullback π (cartierPullback f L)) (cartierPullback π NV) hLNX j hDlin m₀ hm₀ hjm₀
    hLggX hNnefPull hABbig hABfin z hz hc hcq hqz hpolyΦ hcentre hbudget
  have hvy : f v = y := hv
  subst hvy
  obtain ⟨s', v', hs', hv'⟩ := stein_exists_section_generating_of_pullback f happ P v φ hφ g u
    hg hu
  exact ⟨φ, hφ, CartierDivisor.sectionMk _ hs',
    isUnit_cartierLocalCoefficient_sectionMk P (f v) s' hs' φ hφ v' hv'⟩

/-- If the data of the minimizer for relative K-NF exist at every closed point of Y at which P is
not generated by its global sections, for the m₀ given by the ampleness of L, then P is globally
generated. -/
theorem rel_cartierIsGloballyGenerated_of_minimizerData [CompactSpace Y]
    (hn : 1 ≤ n) (hdimV : topologicalKrullDim V = n)
    (hnormV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (hcov : CodimOneChartCovered n K V) {H : CartierDivisor V} (hH : CartierIsAmpleProj K H)
    (cV : EtaleChart K V n) (fV : V.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor V)
    (heff : LogPairBoundaryEffective cV fV d D) (hklt : LogPairIsKlt cV fV d D)
    (f : V ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
    (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
    (P L : CartierDivisor Y) (hL : CartierIsAmpleProj K L)
    (hN : CartierIsAmpleProj K (d • cartierPullback f P - D - cartierPullback f L))
    (hdata : ∀ m₀ : ℕ, 1 ≤ m₀ → ∀ y : Y, IsClosed ({y} : Set Y) →
      (¬ ∃ (φ : Y.functionFieldˣ) (hφ : P.IsLocalEquationAt y φ) (t : Γ(P.sheaf, ⊤)),
        IsUnit (cartierLocalCoefficient P y φ hφ t)) →
      RelIsolationMinimizerData cV fV d D f L m₀ y) :
    CartierIsGloballyGenerated P := by
  obtain ⟨m₀, hm₀, hLgg⟩ := cartierIsAmpleProj_exists_globallyGenerated_divisible_sequence L hL
  apply cartierIsGloballyGenerated_of_forall_isClosed
  intro y hy
  by_contra hgen
  obtain ⟨j, N, s, hs, X, hXi, hXN, hXo, hXp, hXs, π, hdom, hover, hprop, hπ, cX, r, ξ, z, c, q,
    hjm₀, hinj, hξ, hsnc, hBsupp, hDsupp, hz, hc, hcq, hqz, hpolyΦ, hcentre, hbudget⟩ :=
    hdata m₀ hm₀ y hy hgen
  apply hgen
  exact rel_exists_section_generating_of_minimizer_data hn hdimV hnormV hcov hH cV fV d hd D heff
    hklt f happ P L hL hN m₀ hm₀ hLgg y hy j hjm₀ s hs π hπ cX ξ hinj hξ hsnc hBsupp hDsupp z hz hc
    hcq hqz hpolyΦ hcentre hbudget

end Klt

/-- The statement that, under the hypotheses of relative K-NF, the data of the minimizer for
relative K-NF exist, for every m₀, at every closed point of the base at which P is not generated:
the content of sections 2 to 5 and 7 of the manuscript relative to the contraction. -/
def RelMinimizerDataStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D → LogPairIsKlt c₀ f₀ r D →
    ∀ (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
      [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (k : ℕ),
      topologicalKrullDim Y = k → 1 ≤ k →
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered k K Y →
      ∀ (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))],
        (∀ V : Y.Opens, Function.Bijective (f.app V).hom) →
      ∀ P L : CartierDivisor Y, CartierIsAmpleProj K L →
        CartierIsAmpleProj K (r • cartierPullback f P - D - cartierPullback f L) →
        (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
          ((((r * (k + 1) : ℕ) : ℝ) ^ k + δ) * (j : ℝ) ^ k / k.factorial ≤
            cartierRestrictedDim K (j • L) (genericPoint Y))) →
        (∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d → d < k →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
            ((((r * (k + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
              cartierRestrictedDim K (j • L) η)) →
        ∀ m₀ : ℕ, 1 ≤ m₀ → ∀ y : Y, IsClosed ({y} : Set Y) →
          (¬ ∃ (φ : Y.functionFieldˣ) (hφ : P.IsLocalEquationAt y φ) (t : Γ(P.sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient P y φ hφ t)) →
          RelIsolationMinimizerData c₀ f₀ r D f L m₀ y

/-- Relative K-NF follows from the existence of the data of the minimizer for relative K-NF
(the Kawamata–Viehweg theorem in characteristic zero is proved). -/
theorem relativeNumericalFreeness_of_relMinimizerData (hmin : RelMinimizerDataStatement.{u}) :
    RelativeNumericalFreeness.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH₀ c₀ f₀ r hr D heff hklt Y _ _ _ _ k hdimY hk
    hnormY hcovY f _ _ hfapp P L hL hN hvol hsub
  obtain ⟨H, hH⟩ := hH₀
  have hcompact : CompactSpace Y := by
    obtain ⟨m, hm, v, e, hcl, he, -⟩ := hL
    have := polynomialProjectiveToBase_isProper v K
    have : QuasiCompact (Y ↘ Spec (CommRingCat.of K)) := by
      rw [← he]
      infer_instance
    exact QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of K))
  exact rel_cartierIsGloballyGenerated_of_minimizerData hn hdim hnorm hcov hH c₀ f₀ r hr D heff
    hklt f (fun U => (hfapp U).2) P L hL hN
    (fun m₀ hm₀ y hy hgen => hmin K X n hdim hn hnorm hcov ⟨H, hH⟩ c₀ f₀ r hr D heff hklt Y k
      hdimY hk hnormY hcovY f hfapp P L hL hN hvol hsub m₀ hm₀ y hy hgen)

/-- F2 from the base point free theorem for klt pairs and the existence of the data of the
minimizer for relative K-NF; neither Ambro's canonical bundle formula nor any vanishing theorem
beyond the proved Kawamata–Viehweg theorem is used. -/
theorem linearEffectiveFreeness_of_basePointFree_of_relMinimizerData
    (hbpf : KltBasePointFreeStatement.{u}) (hmin : RelMinimizerDataStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_basePointFree_of_relativeNumericalFreeness hbpf
    (relativeNumericalFreeness_of_relMinimizerData hmin)

end MixedFujita
