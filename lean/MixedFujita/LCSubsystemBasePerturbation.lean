/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.HighPowerFixedPartLCPerturbation
public import MixedFujita.FiniteCompleteCartierBaseIdeal
public import MixedFujita.ProjectiveSNCModelPrincipalization
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.EffectiveCartierCoefficientSupport

/-! 元の有限非零線形系から主化を内部構成して基底外klt摂動。 See reports/check-248-high-power-lc-perturbation-complete-base.json for the verified scope. One high residual-power Bertini cut constructs an original effective lc non-klt perturbation klt outside the complete base locus, from one initial nonzero section and a nonempty base. SNC principalization, nonzero fixed part, residual generation, threshold, power and original section descent are internal. A nonempty reduced lower-dimensional non-klt W is internally placed inside that complete base locus without KV. Initial and restricted-section nonvanishing, automatic perturbed adjoint nef-big conditions, usual KV, klt BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra




/-- From an ORIGINAL klt pair and a finite nonzero subsystem with nonempty base,
construct an ORIGINAL lc non-klt effective perturbation which is klt away from
that ACTUAL subsystem base. The SNC model, fixed part, positive threshold,
high multiple and descended section are all constructed internally. -/
theorem exists_lc_nonKlt_high_power_perturbation_klt_outside_subsystem_base
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D)
    (M : CartierDivisor X) {J : Type*} [Finite J] [Nonempty J]
    (s : J → Γ(M.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0)
    (hbase : ((cartierSectionBaseIdeal M s hs).support : Set X).Nonempty) :
    ∃ (a q N : ℕ), 1 ≤ a ∧ 1 ≤ q ∧ N = a + 1 ∧ a < q * N ∧
      ∃ (t : Γ((N • M).sheaf, ⊤)) (ht : t ≠ 0),
        LogPairBoundaryEffective cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) ∧
        LogPairIsLogCanonical cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) ∧
        (¬ LogPairIsKlt cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht)) ∧
        ∀ x : X, x ∉ (cartierSectionBaseIdeal M s hs).support →
          LogPairIsKltOverBasePoint (𝟙 X) x cX fX ((q * N) * d)
            ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) := by
  let A (j : J) := cartierSectionZeroDivisor M (s j) (hs j)
  have hA (j : J) : (A j).IsEffective := cartierSectionZeroDivisor_isEffective M (s j) (hs j)
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, _, hp, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, _, _, _, _, _, F, hF, hFI, hFsupp, _, hfree⟩ :=
    exists_projective_snc_model_principalizing_sum cX fX d D
      (fun i : PEmpty.{1} => i.elim) A hA (fun i : PEmpty.{1} => i.elim) (fun i => i.elim)
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  let I := cartierSectionBaseIdeal M s hs
  have hFI' : effectiveCartierIdealSheaf F hF = I.comap p := hFI
  have hFne : F ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hbase
    obtain ⟨t, ht⟩ := surjective_of_isProper_of_isDominant p x
    have hmem : t ∈ (I.comap p).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change p t ∈ ((cartierSectionBaseIdeal M s hs).support : Set X)
      simpa only [ht] using hx
    rw [← hFI'] at hmem
    have he : effectiveCartierIdealSheaf F hF = ⊤ := by
      subst F
      exact effectiveCartierIdealSheaf_zero_eq_top hF
    rw [he, Scheme.IdealSheafData.support_top] at hmem
    exact hmem
  have hcenters (t : CodimensionOnePoint T) (ht : 0 < cartierCoefficient F (t : T)) :
      p (t : T) ∈ I.support := by
    have hmem : (t : T) ∈ (effectiveCartierIdealSheaf F hF).support := by
      by_contra hn
      rw [cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf F hF _ hn] at ht
      omega
    rw [hFI', Scheme.IdealSheafData.support_comap] at hmem
    exact hmem
  exact exists_lc_nonKlt_high_power_perturbation_klt_outside_fixed_centers p hp hnorm hnormT
    cX fX d hd D heff hklt cT ξ hinj hξ hsnc hsupp M F hF hFne hFsupp
    (hfree M (fun j => cartierIsGloballyGenerated_sub_sectionZeroDivisor M (s j) (hs j))).1
    I.support hcenters

end MixedFujita
