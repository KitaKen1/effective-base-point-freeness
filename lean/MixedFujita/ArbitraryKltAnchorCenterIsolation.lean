/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InternalMinimalLCCenterIsolation
public import MixedFujita.LCCenterDenominatorScaling

/-! 異なる分母のklt基準対から内部孤立化・元L持ち上げ。 See reports/check-268-internal-lc-center-isolation.json for the verified scope. ACTUAL minimal-lc-center isolation now internally constructs the original center ideal finite system, SAME-original-family principalization/residual Bertini, source perturbation, shared SNC model, old-critical positivity and placement. A contained lc center obstructs every positive perturbation, forcing a positive old-critical coefficient on ANY joint model by finite-LC-threshold contradiction. Arbitrary anchor denominators are normalized retaining actual centers. Original positive-numerical klt BPF assumptions construct an isolated restricted-numerical-zero center; EXPLICIT usual H1 KV gives exact-center original mL lifting. Zero-dimensional minimal centers yield original nonvanishing under usual KV. Positive-dimensional numerical-zero-center nonvanishing, general KV, the original nu=0 branch, unconditional BPF and full F1/F2 remain unproved. -/

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


/-- An ARBITRARY-denominator actual effective klt anchor isolates the chosen
minimal lc center internally, preserving the SAME ORIGINAL nef L and all
m>=b ample adjoints. Usual H1 KV then lifts all large ORIGINAL mL to that
EXACT reduced center. No normalization, model, perturbing divisor, finite
system, positive critical prime, placement or center normality is supplied. -/
theorem minimal_lc_center_arbitrary_klt_anchor_isolation_and_original_lifting
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (hn : 1 ≤ n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (hD : LogPairBoundaryEffective c f d D)
    (e : ℕ) (he : 1 ≤ e) (A : CartierDivisor X) (hA : LogPairBoundaryEffective c f e A)
    (hklt : LogPairIsKlt c f e A)
    (Z : Closeds X) (hZ : LogPairIsLogCanonicalCenter c f d D Z)
    (hmin : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f d D V → V ≤ Z → V = Z)
    (L : CartierDivisor X) (hL : CartierIsNef K L) (b : ℕ)
    (hH : CartierIsAmpleProj K ((d * b) • L - D)) :
    ∃ d' : ℕ, 1 ≤ d' ∧ ∃ D' : CartierDivisor X,
      LogPairBoundaryEffective c f d' D' ∧ LogPairIsLogCanonical c f d' D' ∧
      LogPairIsLogCanonicalCenter c f d' D' Z ∧
      (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((d' * m) • L - D')) ∧
      (∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f d' D') ↔ x ∈ Z) ∧
      ∀ (m : ℕ), b ≤ m → ∀ (_ : KawamataViehwegVanishingSNC K n),
        let I := Scheme.IdealSheafData.vanishingIdeal Z
        Subsingleton (Scheme.Modules.Cohomology ((m • L).sheaf ⊗ idealSheafDataModule I) 1) ∧
          (∃ τ : (m • L).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
            ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf),
            Function.Surjective (Scheme.Modules.Hom.app τ ⊤)) ∧
          ∀ t : Γ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf, ⊤), t ≠ 0 →
            ∃ x : X, x ∈ Z ∧ x ∉ cartierBaseLocus (m • L) := by
  have hden : 1 ≤ e * d := Nat.mul_pos (by omega) (by omega)
  have hDs := (logPairBoundaryEffective_scale_denominator_iff c f d e he D).mpr hD
  have hAs : LogPairBoundaryEffective c f (e * d) (d • A) := by
    simpa only [Nat.mul_comm] using (logPairBoundaryEffective_scale_denominator_iff c f e d hd A).mpr hA
  have hklts : LogPairIsKlt c f (e * d) (d • A) := by
    simpa only [Nat.mul_comm] using (logPairIsKlt_scale_denominator_iff c f e d hd A).mpr hklt
  have hZs := (logPairIsLogCanonicalCenter_scale_denominator_iff c f d e he D Z).mpr hZ
  have hmins : ∀ V : Closeds X, LogPairIsLogCanonicalCenter c f (e * d) (e • D) V → V ≤ Z → V = Z := by
    intro V hV hVZ
    exact hmin V ((logPairIsLogCanonicalCenter_scale_denominator_iff c f d e he D V).mp hV) hVZ
  have hHs : CartierIsAmpleProj K (((e * d) * b) • L - e • D) := by
    have heq : ((e * d) * b) • L - e • D = e • ((d * b) • L - D) := by module
    rw [heq]
    exact cartierIsAmpleProj_nsmul hH he
  obtain ⟨d', hd', D', heff', hlc', hZ', hamp, hNK⟩ :=
    minimal_lc_center_klt_anchor_constructs_exact_nonKlt_isolation K hn hnorm c f (e * d) hden (e • D) (d • A)
      hDs hAs hklts Z hZs hmins L hL b hHs
  refine ⟨d', hd', D', heff', hlc', hZ', hamp, hNK, fun m hm hKV => ?_⟩
  have hP : CartierIsAmpleProj K (d' • (m • L) - D') := by simpa only [smul_smul] using hamp m hm
  exact exact_nonKlt_lc_center_restriction_lifting_of_usual_KV K hn hnorm c f d' hd' D' heff' Z hZ' hNK
    ((d * b) • L - D) hH hKV (m • L) (cartierIsAmpleProj_isNef hP)
    (cartierIsAmpleProj_isBig (etaleChart_topologicalKrullDim c) hn hP)

end MixedFujita
