/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.BPFKodairaAmpleBoundary
public import MixedFujita.HighPowerAmpleAdjoint
public import MixedFujita.AmpleIdealSubschemeRestrictionSerre
public import MixedFujita.LCBaseLocusAllMultiples
public import MixedFujita.CartierBigDefinition
public import MixedFujita.CartierNefDefinition

/-! 元BPFから基底集合内W・ample随伴差・集中法用高ねじり切断延長。 See reports/check-250-BPF-ample-boundary-concentration-extension.json for the verified scope. Original nef-big BPF data internally yield a small effective klt boundary increase with an ample adjoint, retaining L and a0. High-power lc adjoints stay ample for all large degrees. Every coherent ideal subscheme has unconditional full Serre vanishing and actual restriction lifting for high ample twists. The fixed nonempty reduced base source and these concentration-twist extensions are internal. Original L lifting still needs explicit usual KV. Initial and restricted L-nonvanishing, minimal-center normality/vanishing, high-multiplicity concentration, usual KV, BPF and full F1/F2 remain unproved. -/

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






/-- ORIGINAL nef-big BPF data construct a small effective klt boundary change,
a nonempty reduced source inside the ACTUAL complete base, and AMPLE adjoints
for every high original multiple. Their high ample twists have unconditional
full Serre vanishing and actual restriction lifting. Ordinary jL lifting still
uses explicit usual KV; initial and restricted L-nonvanishing remain unproved. -/
theorem original_klt_bpf_exists_base_source_ample_adjoints_and_Serre_lifting
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
    ∃ s : ℕ, 2 ≤ s ∧ ∃ G₀ : CartierDivisor X, G₀.IsEffective ∧
      LogPairBoundaryEffective cX fX (s * d) (s • D + G₀) ∧
      LogPairIsKlt cX fX (s * d) (s • D + G₀) ∧
      CartierIsAmpleProj K (((s * d) * a₀) • L - (s • D + G₀)) ∧
      ∃ (a q N : ℕ), 1 ≤ a ∧ 1 ≤ q ∧ N = a + 1 ∧ a < q * N ∧
        ∃ (t : Γ((N • (m • L)).sheaf, ⊤)) (ht : t ≠ 0), ∃ I : X.IdealSheafData,
          I ≠ ⊥ ∧ Nonempty I.subscheme ∧
          topologicalKrullDim I.subscheme ≤ (n - 1 : ℕ) ∧
          (idealSheafDataModule I).IsCoherent ∧ I.radical = I ∧ IsReduced I.subscheme ∧
          I.support ≤ cartierBaseLocus (m • L) ∧
          (∀ x : X, x ∈ (I.support : Set X) ↔ ¬ LogPairIsKltOverBasePoint (𝟙 X) x cX fX ((q * N) * (s * d))
            ((q * N) • (s • D + G₀) + ((s * d) * a) • cartierSectionZeroDivisor (N • (m • L)) t ht)) ∧
          (∀ j : ℕ, a₀ + a * m ≤ j →
            let A := ((q * N) * (s * d)) • (j • L) -
              ((q * N) • (s • D + G₀) + ((s * d) * a) • cartierSectionZeroDivisor (N • (m • L)) t ht)
            CartierIsAmpleProj K A ∧
            ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
              (∀ k : ℕ, Subsingleton (Scheme.Modules.Cohomology ((b • A).sheaf ⊗ idealSheafDataModule I) (k + 1))) ∧
              ∃ r : (b • A).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
                  ((Scheme.Modules.pullback I.subschemeι).obj (b • A).sheaf),
                Function.Surjective (Scheme.Modules.Hom.app r ⊤)) ∧
          ∀ (_ : KawamataViehwegVanishingSNC K n), ∀ j : ℕ, a₀ + a * m ≤ j →
            Subsingleton (Scheme.Modules.Cohomology ((j • L).sheaf ⊗ idealSheafDataModule I) 1) ∧
            ∃ r : (j • L).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
                ((Scheme.Modules.pullback I.subschemeι).obj (j • L).sheaf),
              Function.Surjective (Scheme.Modules.Hom.app r ⊤) ∧
              ∀ u : Γ((Scheme.Modules.pullback I.subschemeι).obj (j • L).sheaf, ⊤), u ≠ 0 →
                ∃ x : X, x ∈ (I.support : Set X) ∧ x ∉ cartierBaseLocus (j • L) := by
  obtain ⟨s, hs, G₀, hG₀, heff₀, hklt₀, hA₀⟩ :=
    original_klt_bpf_exists_small_effective_boundary_ample_adjoint K hdim hn hnorm hProj
      cX fX d hd D heff hklt L a₀ hnef hbig
  have hsd : 1 ≤ s * d := Nat.mul_pos (by omega) (by omega)
  have hnef₀ := cartierIsAmpleProj_isNef hA₀
  have hbig₀ := cartierIsAmpleProj_isBig hdim hn hA₀
  obtain ⟨a, q, N, ha, hq, hN, hsmall, t, ht, I, hI, hW, _, hdimW, hcoh, hIr, hred, hplace, hNK, hLift⟩ :=
    original_klt_bpf_exists_base_subscheme_all_large_multiples_lift K hdim hn hnorm hcov hProj
      cX fX (s * d) hsd (s • D + G₀) heff₀ hklt₀ L hL a₀ hnef₀ hbig₀ m s₀ hs₀ hbase
  let := hcoh
  refine ⟨s, hs, G₀, hG₀, heff₀, hklt₀, hA₀, a, q, N, ha, hq, hN, hsmall, t, ht,
    I, hI, hW, hdimW, hcoh, hIr, hred, hplace, hNK, ?_, hLift⟩
  intro j hj
  have hNpos : 1 ≤ N := by omega
  have hA := original_ample_bpf_high_power_perturbed_adjoint_isAmple K L (s • D + G₀)
    hL (s * d) a₀ hA₀ a q N m j hq hNpos hj t ht
  exact ⟨hA, ample_ideal_subscheme_all_high_twists_serre_and_restriction _ hA I⟩

end MixedFujita
