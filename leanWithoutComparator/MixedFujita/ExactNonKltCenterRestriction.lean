/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogCanonicalCenters
public import MixedFujita.LCNonKltClosedSubscheme
public import MixedFujita.NormalCodimensionOneCharts

/-! 正確な被約lc中心イデアル同定と通常KVによる制限持ち上げ。 See reports/check-267-klt-anchor-center-isolation.json for the verified scope. A fixed rational perturbation ratio and all-large mixing with an actual klt anchor retain only OLD positive-perturbation critical components and preserve ORIGINAL L ample adjoints. On a SUPPLIED actual shared proper SNC model with a SUPPLIED actual effective source perturbation and critical-placement/positivity inputs, the entire ORIGINAL nonKlt locus equals the chosen minimal lc center. The exact reduced center ideal is internally identified, and EXPLICIT usual H1 KV yields original Cartier and all-large ORIGINAL mL restriction lifting. Constructing the isolation perturbation/model/placement/positivity and numerical-zero center nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- When the ENTIRE actual non-klt locus equals a chosen actual lc center,
usual H1 KV yields vanishing for that EXACT REDUCED CENTER IDEAL and actual
surjective original Cartier restriction. Nonzero center sections then produce
points outside the ORIGINAL base locus. No center normality, subadjunction,
supplied ideal/kernel identification or restriction map is assumed. -/
theorem exact_nonKlt_lc_center_restriction_lifting_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (hNK : ∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d D) ↔ x ∈ Z)
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (hKV : KawamataViehwegVanishingSNC K n)
    (P : CartierDivisor X) (hnef : CartierIsNef K (d • P - D)) (hbig : CartierIsBig K (d • P - D)) :
    let I := Scheme.IdealSheafData.vanishingIdeal Z
    Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ idealSheafDataModule I) 1) ∧
      (∃ ρ : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf),
        Function.Surjective (Scheme.Modules.Hom.app ρ ⊤)) ∧
      ∀ t : Γ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf, ⊤), t ≠ 0 →
        ∃ x : X, x ∈ Z ∧ x ∉ cartierBaseLocus P := by
  dsimp only
  obtain ⟨x₀, hx₀⟩ := (logPairIsLogCanonicalCenter_isIrreducible c f d D Z hZ).nonempty
  have hnot : ¬ LogPairIsKlt c f d D := by
    intro h
    exact (hNK x₀).mpr hx₀ (((logPairIsKlt_iff_forall_basePoint (𝟙 X) c f d D).mp h) x₀)
  have hcov : CodimOneChartCovered n K X :=
    normal_codimOneChartCovered (K := K) (etaleChart_topologicalKrullDim c) hnorm
  obtain ⟨I, _, _, _, _, _, hIr, _, _, hpoints, _, _, hLift⟩ :=
    lc_pair_exists_unique_reduced_nonKlt_subscheme K hn hnorm hcov ⟨H, hH⟩ c f d hd D heff hZ.1 hnot
  have hsupp : I.support = Z := by
    ext x
    exact (hpoints x).trans (hNK x)
  have hIeq : I = Scheme.IdealSheafData.vanishingIdeal Z := by
    rw [← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hIr]
  obtain ⟨hvan, ρ, hρ, hsec⟩ := hLift hKV P hnef hbig
  have hsec' : ∀ t : Γ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf, ⊤), t ≠ 0 →
      ∃ x : X, x ∈ Z ∧ x ∉ cartierBaseLocus P := by
    intro t ht
    obtain ⟨x, hx, hbase⟩ := hsec t ht
    exact ⟨x, hsupp ▸ hx, hbase⟩
  have hsurj : ∃ ρ : P.sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj P.sheaf),
      Function.Surjective (Scheme.Modules.Hom.app ρ ⊤) := ⟨ρ, hρ⟩
  rw [hIeq] at hvan hsec' hsurj
  exact ⟨hvan, hsurj, hsec'⟩

end MixedFujita
