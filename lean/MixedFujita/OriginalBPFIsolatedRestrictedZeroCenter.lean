/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ArbitraryKltAnchorCenterIsolation
public import MixedFujita.OriginalBPFRestrictedZeroCenter

/-! 元BPF正νから孤立した制限ν0中心と通常KV元mL持ち上げ。 See reports/check-268-internal-lc-center-isolation.json for the verified scope. ACTUAL minimal-lc-center isolation now internally constructs the original center ideal finite system, SAME-original-family principalization/residual Bertini, source perturbation, shared SNC model, old-critical positivity and placement. A contained lc center obstructs every positive perturbation, forcing a positive old-critical coefficient on ANY joint model by finite-LC-threshold contradiction. Arbitrary anchor denominators are normalized retaining actual centers. Original positive-numerical klt BPF assumptions construct an isolated restricted-numerical-zero center; EXPLICIT usual H1 KV gives exact-center original mL lifting. Zero-dimensional minimal centers yield original nonvanishing under usual KV. Positive-dimensional numerical-zero-center nonvanishing, general KV, the original nu=0 branch, unconditional BPF and full F1/F2 remain unproved. -/

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


/-- ORIGINAL normal klt BPF assumptions with POSITIVE ORIGINAL numerical
dimension construct a lower-dimensional RESTRICTED-NUMERICAL-ZERO center
which is the ENTIRE actual non-klt locus of an internally constructed effective
lc pair. ALL large ORIGINAL L-adjoints stay ample; explicit usual H1 KV gives
restriction lifting to that EXACT center for all large ORIGINAL mL. No initial
L section, center/model/perturbation, numerical-zero endpoint, isolation or
center-normality input is supplied. Restricted nonvanishing and general KV
are NOT concluded. -/
theorem original_klt_BPF_positive_numerical_constructs_isolated_restricted_zero_center_and_lifting
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 2 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) (L : CartierDivisor X) (hL : CartierIsNef K L)
    (a₀ : ℕ) (hnef : CartierIsNef K ((d * a₀) • L - D))
    (hbig : CartierIsBig K ((d * a₀) • L - D))
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hν : 1 ≤ cartierNumericalDimension K n hdim L J) :
    ∃ r b : ℕ, 1 ≤ r ∧ ∃ (D' : CartierDivisor X) (η : X)
      (_ : IsProper (pointClosureScheme η ↘ Spec (CommRingCat.of K))),
      LogPairBoundaryEffective c f r D' ∧ LogPairIsLogCanonical c f r D' ∧
      LogPairIsLogCanonicalCenter c f r D' ⟨closure ({η} : Set X), isClosed_closure⟩ ∧
      (∀ x : X, (¬ LogPairIsKltOverBasePoint (𝟙 X) x c f r D') ↔ x ∈ closure ({η} : Set X)) ∧
      (∀ m : ℕ, b ≤ m → CartierIsAmpleProj K ((r * m) • L - D')) ∧
      topologicalKrullDim (pointClosureScheme η) ≤ (n - 1 : ℕ) ∧
      (∀ (k : ℕ) (hdimZ : topologicalKrullDim (pointClosureScheme η) = k)
        (LZ HZ : CartierDivisor (pointClosureScheme η))
        (_aL : (Scheme.Modules.pullback (pointClosureι η)).obj L.sheaf ≅ LZ.sheaf),
        CartierIsAmpleProj K HZ → cartierNumericalDimension K k hdimZ LZ HZ = 0) ∧
      ∀ (m : ℕ), b ≤ m → ∀ (_ : KawamataViehwegVanishingSNC K n),
        let I := pointClosureIdeal η
        Subsingleton (Scheme.Modules.Cohomology ((m • L).sheaf ⊗ idealSheafDataModule I) 1) ∧
          (∃ τ : (m • L).sheaf ⟶ (Scheme.Modules.pushforward I.subschemeι).obj
            ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf),
            Function.Surjective (Scheme.Modules.Hom.app τ ⊤)) ∧
          ∀ t : Γ((Scheme.Modules.pullback I.subschemeι).obj (m • L).sheaf, ⊤), t ≠ 0 →
            ∃ x : X, x ∈ closure ({η} : Set X) ∧ x ∉ cartierBaseLocus (m • L) := by
  obtain ⟨r₀, b, hr₀, D₀, η, hproper, heff₀, _, _, hamp₀, hZ₀, hmin, _, hdimZ, hzero⟩ :=
    original_klt_BPF_positive_numerical_exists_restricted_numerical_zero_lc_center K n hdim hn hnorm
      c f d hd D heff hklt L hL a₀ hnef hbig J hJ hν
  let := hproper
  obtain ⟨r, hr, D', heff', hlc', hZ, hamp, hNK, hLift⟩ :=
    minimal_lc_center_arbitrary_klt_anchor_isolation_and_original_lifting K (by omega) hnorm c f r₀ hr₀ D₀ heff₀
      d hd D heff hklt ⟨closure ({η} : Set X), isClosed_closure⟩ hZ₀ hmin L hL b (hamp₀ b le_rfl)
  refine ⟨r, b, hr, D', η, hproper, heff', hlc', hZ, ?_, hamp, hdimZ, hzero, ?_⟩
  · intro x
    exact hNK x
  · intro m hm hKV
    exact hLift m hm hKV

end MixedFujita
