/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LCCompleteBasePerturbation
public import MixedFujita.OriginalBPFHighPowerAdjointPositivity
public import MixedFujita.ReducedClosedBaseRestrictionVanishing

/-! 元BPF全大倍数の持ち上げと安定power基底集合の制限切断零性。 See reports/check-249-original-BPF-adjoint-all-multiples-stable-restriction.json for the verified scope. Original BPF positivity internally supplies all sufficiently large perturbed-adjoint nef-big conditions, with an explicit coarse natural degree bound. A fixed nonempty reduced W inside the complete base locus has usual-KV-based actual H1 vanishing and restriction surjectivity for every large original multiple. For a supplied stable nonempty power base and an actual initial seed, all high power restricted section spaces on W are zero. Initial and restricted-section nonvanishing, usual KV, klt BPF and full F1/F2 remain unproved. -/

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





/-- ORIGINAL BPF adjoint positivity supplies one actual reduced non-klt source
inside B(mL), and usual KV gives actual restriction lifting for ALL sufficiently
large ORIGINAL multiples jL. No perturbed-adjoint positivity is supplied. -/
theorem original_klt_bpf_exists_base_subscheme_all_large_multiples_lift
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (L : CartierDivisor X) (hL : CartierIsNef K L)
    (a₀ : ℕ) (hnef : CartierIsNef K ((d * a₀) • L - D))
    (hbig : CartierIsBig K ((d * a₀) • L - D)) (m : ℕ)
    (s₀ : Γ((m • L).sheaf, ⊤)) (hs₀ : s₀ ≠ 0)
    (hbase : (cartierBaseLocus (m • L) : Set X).Nonempty) :
    ∃ (a q N : ℕ), 1 ≤ a ∧ 1 ≤ q ∧ N = a + 1 ∧ a < q * N ∧
      ∃ (t : Γ((N • (m • L)).sheaf, ⊤)) (ht : t ≠ 0), ∃ I : X.IdealSheafData,
        I ≠ ⊥ ∧ Nonempty I.subscheme ∧ genericPoint X ∉ (I.support : Set X) ∧
        topologicalKrullDim I.subscheme ≤ (n - 1 : ℕ) ∧
        (idealSheafDataModule I).IsCoherent ∧ I.radical = I ∧ IsReduced I.subscheme ∧
        I.support ≤ cartierBaseLocus (m • L) ∧
        (∀ x : X, x ∈ (I.support : Set X) ↔ ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX ((q * N) * d)
          ((q * N) • D + (d * a) • cartierSectionZeroDivisor (N • (m • L)) t ht)) ∧
        ∀ (_ : KawamataViehwegVanishingSNC K n), ∀ j : ℕ, a₀ + a * m ≤ j →
          Subsingleton (Scheme.Modules.Cohomology ((j • L).sheaf ⊗ idealSheafDataModule I) 1) ∧
          ∃ r : (j • L).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
              ((Scheme.Modules.pullback I.subschemeι).obj (j • L).sheaf),
            Function.Surjective (Scheme.Modules.Hom.app r ⊤) ∧
            ∀ s : Γ((Scheme.Modules.pullback I.subschemeι).obj (j • L).sheaf, ⊤), s ≠ 0 →
              ∃ x : X, x ∈ (I.support : Set X) ∧ x ∉ cartierBaseLocus (j • L) := by
  obtain ⟨a, q, N, ha, hq, hN, hsmall, t, ht, I, hI, hW, hgen, hdimW, hcoh, hIr, hred,
      hplace, hNK, hLift⟩ := klt_pair_exists_reduced_nonKlt_subscheme_inside_complete_base_locus
    K hn hnorm hcov hProj cX fX d hd D heff hklt (m • L) s₀ hs₀ hbase
  refine ⟨a, q, N, ha, hq, hN, hsmall, t, ht, I, hI, hW, hgen, hdimW, hcoh, hIr, hred, hplace, hNK, ?_⟩
  intro hKV j hj
  have hNpos : 1 ≤ N := by omega
  have hpositive := original_bpf_perturbed_adjoint_nef_big_of_degree_bound
    K n hdim hn hnorm L D hL d a₀ hnef hbig a q N m j hq hNpos hj t ht
  exact hLift hKV (j • L) hpositive.1 hpositive.2


/-- For a supplied stable nonempty power base locus with an actual initial seed,
ORIGINAL BPF inputs construct a fixed nonempty reduced W in that locus. Usual KV
makes every sufficiently high power restrict SURJECTIVELY to the ZERO section
space on W. Actual restricted-section nonvanishing is the remaining contradiction. -/
theorem original_klt_bpf_stable_power_base_constructs_reduced_source_zero_restrictions
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (L : CartierDivisor X) (hL : CartierIsNef K L)
    (a₀ : ℕ) (hnef : CartierIsNef K ((d * a₀) • L - D))
    (hbig : CartierIsBig K ((d * a₀) • L - D)) (b e : ℕ) (hb : 2 ≤ b)
    (hstable : ∀ f : ℕ, e ≤ f → cartierBaseLocus ((b ^ f) • L) = cartierBaseLocus ((b ^ e) • L))
    (s₀ : Γ(((b ^ e) • L).sheaf, ⊤)) (hs₀ : s₀ ≠ 0)
    (hbase : (cartierBaseLocus ((b ^ e) • L) : Set X).Nonempty) :
    ∃ I : X.IdealSheafData, Nonempty I.subscheme ∧
      topologicalKrullDim I.subscheme ≤ (n - 1 : ℕ) ∧
      (idealSheafDataModule I).IsCoherent ∧ I.radical = I ∧ IsReduced I.subscheme ∧
      I.support ≤ cartierBaseLocus ((b ^ e) • L) ∧
      ∃ f₀ : ℕ, e ≤ f₀ ∧ ∀ (_ : KawamataViehwegVanishingSNC K n), ∀ f : ℕ, f₀ ≤ f →
        Subsingleton (Scheme.Modules.Cohomology (((b ^ f) • L).sheaf ⊗ idealSheafDataModule I) 1) ∧
        Subsingleton Γ((Scheme.Modules.pullback I.subschemeι).obj ((b ^ f) • L).sheaf, ⊤) ∧
        ∃ r : ((b ^ f) • L).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
            ((Scheme.Modules.pullback I.subschemeι).obj ((b ^ f) • L).sheaf),
          Function.Surjective (Scheme.Modules.Hom.app r ⊤) := by
  obtain ⟨a, q, N, _, _, _, _, t, ht, I, _, hW, _, hdimW, hcoh, hIr, hred, hplace, _, hLift⟩ :=
    original_klt_bpf_exists_base_subscheme_all_large_multiples_lift K hdim hn hnorm hcov hProj
      cX fX d hd D heff hklt L hL a₀ hnef hbig (b ^ e) s₀ hs₀ hbase
  let := hred
  have hpow (f : ℕ) : f ≤ b ^ f := by
    induction f with
    | zero => simp
    | succ f ih =>
      rw [pow_succ]
      have hone : 1 ≤ b ^ f := one_le_pow₀ (by omega)
      nlinarith
  refine ⟨I, hW, hdimW, hcoh, hIr, hred, hplace, max e (a₀ + a * b ^ e), le_max_left _ _, ?_⟩
  intro hKV f hf
  have hef : e ≤ f := (le_max_left _ _).trans hf
  have hj : a₀ + a * b ^ e ≤ b ^ f := (le_max_right _ _).trans (hf.trans (hpow f))
  obtain ⟨hvan, r, hr, _⟩ := hLift hKV (b ^ f) hj
  have hplace' : I.support ≤ cartierBaseLocus ((b ^ f) • L) := by
    rw [hstable f hef]
    exact hplace
  exact ⟨hvan, reduced_closed_base_locus_restriction_sections_subsingleton I _ r hr hplace', r, hr⟩

end MixedFujita
