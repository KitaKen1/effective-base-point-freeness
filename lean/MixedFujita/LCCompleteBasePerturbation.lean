/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCSubsystemBasePerturbation
public import MixedFujita.FiniteCompleteCartierBaseIdeal
public import MixedFujita.LCNonKltClosedSubscheme

/-! 元の完全線形系の基底集合内に非空被約非klt閉部分源を内部構成。 See reports/check-248-high-power-lc-perturbation-complete-base.json for the verified scope. One high residual-power Bertini cut constructs an original effective lc non-klt perturbation klt outside the complete base locus, from one initial nonzero section and a nonempty base. SNC principalization, nonzero fixed part, residual generation, threshold, power and original section descent are internal. A nonempty reduced lower-dimensional non-klt W is internally placed inside that complete base locus without KV. Initial and restricted-section nonvanishing, automatic perturbed adjoint nef-big conditions, usual KV, klt BPF and full F1/F2 remain unproved. -/

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




/-- A single nonzero section and a nonempty COMPLETE Cartier base locus suffice
for an internally constructed lc non-klt perturbation which is klt outside that
complete base locus. No finite subsystem or SNC/principalization input remains. -/
theorem exists_lc_nonKlt_high_power_perturbation_klt_outside_complete_base_locus
    {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D)
    (M : CartierDivisor X) (s₀ : Γ(M.sheaf, ⊤)) (hs₀ : s₀ ≠ 0)
    (hbase : (cartierBaseLocus M : Set X).Nonempty) :
    ∃ (a q N : ℕ), 1 ≤ a ∧ 1 ≤ q ∧ N = a + 1 ∧ a < q * N ∧
      ∃ (t : Γ((N • M).sheaf, ⊤)) (ht : t ≠ 0),
        LogPairBoundaryEffective cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) ∧
        LogPairIsLogCanonical cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) ∧
        (¬ LogPairIsKlt cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht)) ∧
        ∀ x : X, x ∉ cartierBaseLocus M →
          LogPairIsKltOverBasePoint (𝟙 X) x cX fX ((q * N) * d)
            ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht) := by
  obtain ⟨r, hr, s, hs, hI⟩ := exists_finite_nonzero_Cartier_subsystem_same_complete_base_locus (K := K) M s₀ hs₀
  let : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  have hbase' : ((cartierSectionBaseIdeal M s hs).support : Set X).Nonempty := by
    simpa only [hI] using hbase
  obtain ⟨a, q, N, ha, hq, hN, hsmall, t, ht, he, hlc, hnot, haway⟩ :=
    exists_lc_nonKlt_high_power_perturbation_klt_outside_subsystem_base
      hnorm cX fX d hd D heff hklt M s hs hbase'
  exact ⟨a, q, N, ha, hq, hN, hsmall, t, ht, he, hlc, hnot, by simpa only [hI] using haway⟩


/-- An ORIGINAL klt pair, one nonzero section and a nonempty complete base locus
construct a nonempty reduced non-klt subscheme INSIDE THAT COMPLETE BASE LOCUS.
All models, perturbations and the ideal are internal. Usual KV is quantified only
for subsequent lifting; nonvanishing of the restricted adjoint is still unproved. -/
theorem klt_pair_exists_reduced_nonKlt_subscheme_inside_complete_base_locus
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D)
    (M : CartierDivisor X) (s₀ : Γ(M.sheaf, ⊤)) (hs₀ : s₀ ≠ 0)
    (hbase : (cartierBaseLocus M : Set X).Nonempty) :
    ∃ (a q N : ℕ), 1 ≤ a ∧ 1 ≤ q ∧ N = a + 1 ∧ a < q * N ∧
      ∃ (t : Γ((N • M).sheaf, ⊤)) (ht : t ≠ 0), ∃ I : X.IdealSheafData,
        I ≠ ⊥ ∧ Nonempty I.subscheme ∧ genericPoint X ∉ (I.support : Set X) ∧
        topologicalKrullDim I.subscheme ≤ (n - 1 : ℕ) ∧
        (idealSheafDataModule I).IsCoherent ∧ I.radical = I ∧ IsReduced I.subscheme ∧
        I.support ≤ cartierBaseLocus M ∧
        (∀ x : X, x ∈ (I.support : Set X) ↔ ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht)) ∧
        ∀ (_ : KawamataViehwegVanishingSNC K n), ∀ P : CartierDivisor X,
          CartierIsNef K (((q * N) * d) • P -
            ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht)) →
          CartierIsBig K (((q * N) * d) • P -
            ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht)) →
          Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1) ∧
          ∃ r : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
              ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf),
            Function.Surjective (Scheme.Modules.Hom.app r ⊤) ∧
            ∀ s : Γ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf, ⊤), s ≠ 0 →
              ∃ x : X, x ∈ (I.support : Set X) ∧ x ∉ cartierBaseLocus P := by
  obtain ⟨a, q, N, ha, hq, hN, hsmall, t, ht, heff', hlc', hnot', haway⟩ :=
    exists_lc_nonKlt_high_power_perturbation_klt_outside_complete_base_locus
      hnorm cX fX d hd D heff hklt M s₀ hs₀ hbase
  have hNpos : 1 ≤ N := by omega
  have hden : 1 ≤ (q * N) * d := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  obtain ⟨I, hI, hW, hgen, hdim, hcoh, hIr, hred, _, hNK, _, hPlace, hLift⟩ :=
    lc_pair_exists_unique_reduced_nonKlt_subscheme K hn hnorm hcov hProj cX fX
      ((q * N) * d) hden ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • M) t ht)
      heff' hlc' hnot'
  exact ⟨a, q, N, ha, hq, hN, hsmall, t, ht, I, hI, hW, hgen, hdim, hcoh, hIr, hred,
    (hPlace (cartierBaseLocus M)).mpr haway, hNK, hLift⟩

end MixedFujita
